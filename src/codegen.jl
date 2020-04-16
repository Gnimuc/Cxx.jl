

struct JLCppCast{T,JLT}
    data::JLT
end
@generated function JLCppCast{T}(data::JLT) where {T,JLT}
    JLT.mutable ||
        error("Can only pass pointers to mutable values. " *
              "To pass immutables, use an array instead.")
    quote
        JLCppCast{T,JLT}(data)
    end
end

# Represents a forced cast form the value T
# (which may be any C++ compatible value)
# to the the C++ type To
struct CppCast{T,To}
    from::T
end
CppCast(from::T,::Type{To}) where {T,To} = CppCast{T,To}(from)
cast(from::T,::Type{To}) where {T,To} = CppCast{T,To}(from)

# Represents a C++ Deference
struct CppDeref{T}
    val::T
end

# Represent a C++ addrof (&foo)
struct CppAddr{T}
    val::T
end

stripmodifier(cppfunc::Type{CppFptr{f}}) where {f} = cppfunc
stripmodifier(p::Union{Type{CppPtr{T,CVR}},
    Type{CppRef{T,CVR}}}) where {T,CVR} = p
stripmodifier(p::Type{T}) where {T <: CppValue} = p
stripmodifier(p::Type{T}) where {T<:CppEnum} = p
stripmodifier(p::CxxBuiltinTypes) = p
stripmodifier(p::Type{T}) where {T<:Function} = p
stripmodifier(p::Type{Ptr{T}}) where {T} = p
stripmodifier(p::Type{T}) where {T<:Ref} = p
stripmodifier(p::Type{JLCppCast{T,JLT}}) where {T,JLT} = p
stripmodifier(p::Type{T}) where {T} = p

resolvemodifier(C,p::Union{Type{CppPtr{T,CVR}}, Type{CppRef{T,CVR}}}, e::pcpp"clang::Expr") where {T,CVR} = e
resolvemodifier(C, p::Type{T}, e::pcpp"clang::Expr") where {T <: CppValue} = e
resolvemodifier(C,p::CxxBuiltinTypes, e::pcpp"clang::Expr") = e
resolvemodifier(C,p::Type{Ptr{T}}, e::pcpp"clang::Expr") where {T} = e
resolvemodifier(C,p::Type{T}, e::pcpp"clang::Expr") where {T<:Ref} = e
resolvemodifier(C,p::Type{T}, e::pcpp"clang::Expr") where {T<:CppEnum} = e
resolvemodifier(C,cppfunc::Type{CppFptr{f}}, e::pcpp"clang::Expr") where {f} = e
resolvemodifier(C,p::Type{JLCppCast{T,JLT}}, e::pcpp"clang::Expr") where {T,JLT} = e
resolvemodifier(C,p::Type{T}, e::pcpp"clang::Expr") where {T} = e

# For everything else, perform the appropriate transformation
stripmodifier(p::Type{CppCast{T,To}}) where {T,To} = T
stripmodifier(p::Type{CppDeref{T}}) where {T} = T
stripmodifier(p::Type{CppAddr{T}}) where {T} = T

resolvemodifier(C,p::Type{CppCast{T,To}}, e::pcpp"clang::Expr") where {T,To} =
    createCast(C,e,cpptype(C,To),CK_BitCast)
resolvemodifier(C,p::Type{CppDeref{T}}, e::pcpp"clang::Expr") where {T} =
    createDerefExpr(C,e)
resolvemodifier(C,p::Type{CppAddr{T}}, e::pcpp"clang::Expr") where {T} =
    CreateAddrOfExpr(C,e)

function irbuilder(C)
    pcpp"clang::CodeGen::CGBuilderTy"(
        ccall((:clang_get_builder,libcxxffi),Ptr{Cvoid},(Ref{ClangCompiler},),C))
end

function _julia_to_llvm(@nospecialize x)
    isboxed = Ref{UInt8}()
    ty = pcpp"llvm::Type"(ccall(:jl_type_to_llvm,Ptr{Cvoid},(Any,Ref{UInt8}),x,isboxed))
    (isboxed[] != 0, ty)
end
function julia_to_llvm(@nospecialize x)
    isboxed, ty = _julia_to_llvm(x)
    isboxed ? getPRJLValueTy() : ty
end

cxxtransform(T,ex) = (T, ex)
cxxtransform(::Type{String},ex) = (Ptr{UInt8},:(pointer($ex)))

function buildargexprs(C, argt; derefval = true)
    callargs = pcpp"clang::Expr"[]
    pvds = pcpp"clang::ParmVarDecl"[]
    for i in 1:length(argt)
        t = argt[i]
        st = stripmodifier(t)
        argit = cpptype(C, st)
        st <: CppValue && (argit = pointerTo(C,argit))
        argpvd = CreateParmVarDecl(C, argit)
        push!(pvds, argpvd)
        expr = CreateDeclRefExpr(C, argpvd)
        derefval && st <: CppValue && (expr = createDerefExpr(C, expr))
        expr = resolvemodifier(C, t, expr)
        push!(callargs,expr)
    end
    callargs, pvds
end

# Emits either a CallExpr, a NewExpr, or a CxxConstructExpr, depending on which
# one is non-NULL
function EmitExpr(C,ce,nE,ctce, argt, pvds, rett = Cvoid; kwargs...)
    builder = irbuilder(C)
    argt = Type[argt...]
    map!(argt, argt) do x
        (isCxxEquivalentType(x) || x <: CxxBuiltinTs) ? x : Ref{x}
    end
    llvmargt = Type[argt...]
    issret = false
    rslot = C_NULL
    rt = C_NULL
    ret = C_NULL

    if ce != C_NULL
        # First we need to get the return type of the C++ expression
        rt = BuildDecltypeType(C,ce)
        rett = juliatype(rt)

        issret = (rett != Union{}) && rett <: CppValue
    elseif ctce != C_NULL
        issret = true
        rt = GetExprResultType(ctce)
    end

    if issret
        pushfirst!(llvmargt,rett)
    end

    llvmrt = julia_to_llvm(rett)
    # Let's create an LLVM function
    f = CreateFunction(C, issret ? julia_to_llvm(Cvoid) : llvmrt,
        map(julia_to_llvm,llvmargt))

    # Clang's code emitter needs some extra information about the function, so let's
    # initialize that as well
    state = setup_cpp_env(C,f)

    builder = irbuilder(C)

    # First compute the llvm arguments (unpacking them from their julia wrappers),
    # then associate them with the clang level variables
    args = llvmargs(C, builder, f, llvmargt)
    associateargs(C, builder, argt, issret ? args[2:end] : args,pvds)

    if ce != C_NULL
        if issret
            rslot = CreateBitCast(builder,args[1],getPointerTo(toLLVM(C,rt)))
        end
        MarkDeclarationsReferencedInExpr(C,ce)
        ret = EmitCallExpr(C,ce,rslot)
        if rett <: CppValue
            ret = C_NULL
        end
    elseif nE != C_NULL
        ret = EmitCXXNewExpr(C,nE)
    elseif ctce != C_NULL
        MarkDeclarationsReferencedInExpr(C,ctce)
        EmitAnyExprToMem(C,ctce,args[1],true)
    end

    # Common return path for everything that's calling a normal function
    # (i.e. everything but constructors)
    createReturn(C,builder,f,argt,llvmargt,llvmrt,rett,rt,ret,state; kwargs...)
end

function createReturn(C,builder,f,argt,llvmargt,llvmrt,rett,rt,ret,state; argidxs = [1:length(argt);], symargs = nothing)
    argt = Type[argt...]

    jlrt = rett
    if ret == C_NULL
        jlrt = Cvoid
        CreateRetVoid(builder)
    else
        if rett == Cvoid || isVoidTy(llvmrt)
            CreateRetVoid(builder)
        else
            if rett <: CppEnum || rett <: CppFptr
                undef = getUndefValue(llvmrt)
                elty = getStructElementType(llvmrt,0)
                ret = rett <: CppFptr ?
                    PtrToInt(builder, ret, elty) :
                    CreateBitCast(builder, ret, elty)
                ret = InsertValue(builder, undef, ret, 0)
            elseif rett <: CppRef || rett <: CppPtr || rett <: Ptr
                ret = PtrToInt(builder, ret, llvmrt)
            elseif rett == Bool
                ret = CreateZext(builder,ret,julia_to_llvm(rett))
            else
                ret = CreateBitCast(builder,ret,julia_to_llvm(rett))
            end
            CreateRet(builder,ret)
        end
    end

    # cleanup_cpp_env(C,state)

    args2 = Any[]
    for (j,i) = enumerate(argidxs)
        if symargs === nothing
            arg = :(args[$i])
        else
            arg = symargs[i]
        end
        if argt[j] <: JLCppCast
            push!(args2,:($arg.data))
            argt[j] = CppPtr{argt[i].parameters[1]}
        else
            push!(args2,arg)
        end
    end

    if (rett != Union{}) && rett <: CppValue
        arguments = vcat([:r], args2)
        size = cxxsizeof(C,rt)
        B = Expr(:block,
            :( r = ($(rett){$(Int(size))})() ),
                Expr(:call,Core.Intrinsics.llvmcall,convert(Ptr{Cvoid},f),Cvoid,Tuple{llvmargt...},arguments...))
        T = cpptype(C, rett)
        D = getAsCXXRecordDecl(T)
        if D != C_NULL && !hasTrivialDestructor(C,D)
            # Need to call the destructor
            push!(B.args,:( finalizer($(get_destruct_for_instance(C)), r) ))
        end
        push!(B.args,:r)
        return B
    else
        return Expr(:call,Core.Intrinsics.llvmcall,convert(Ptr{Cvoid},f),rett,Tuple{argt...},args2...)
    end
end

function llvmargs(C, builder, f, argt)
    args = Vector{pcpp"llvm::Value"}(undef, length(argt))
    for i in 1:length(argt)
        t = argt[i]
        args[i] = pcpp"llvm::Value"(ccall(
            (:get_nth_argument,libcxxffi),Ptr{Cvoid},(Ptr{Cvoid},Csize_t),f,i-1))
        @assert args[i] != C_NULL
        args[i] = resolvemodifier_llvm(C, builder, t, args[i])
        if args[i] == C_NULL
            error("Failed to process argument")
        end
    end
    args
end

resolvemodifier_llvm(C, builder, t::Type{Ptr{ptr}}, v::pcpp"llvm::Value") where {ptr} = IntToPtr(builder,v,toLLVM(C,cpptype(C, Ptr{ptr})))
function resolvemodifier_llvm(C, builder, t::Type{T}, v::pcpp"llvm::Value") where {T<:Ref}
    v = CreatePointerFromObjref(C, builder, v)
    v
end
resolvemodifier_llvm(C, builder, t::Type{Bool}, v::pcpp"llvm::Value") =
    CreateTrunc(builder, v, toLLVM(C, cpptype(C, Bool)))
resolvemodifier_llvm(C, builder, t::CxxBuiltinTypes, v::pcpp"llvm::Value") = v

resolvemodifier_llvm(C, builder, t::Type{T}, v::pcpp"llvm::Value") where {T} = v

function resolvemodifier_llvm(C, builder,
    t::Type{CppRef{T,CVR}}, v::pcpp"llvm::Value") where {T,CVR}
    ty = cpptype(C, t)
    IntToPtr(builder,v,toLLVM(C,ty))
end

function resolvemodifier_llvm(C, builder, t::Type{CppPtr{T, CVR}}, v::pcpp"llvm::Value") where {T,CVR}
    ty = cpptype(C, t)
    IntToPtr(builder,v,getPointerTo(toLLVM(C,ty)))
end

# Same situation as the pointer case
resolvemodifier_llvm(C, builder, t::Type{T}, v::pcpp"llvm::Value") where {T<:CppEnum} =
    ExtractValue(C,v,0)
resolvemodifier_llvm(C, builder, t::Type{CppFptr{f}}, v::pcpp"llvm::Value") where {f} =
    ExtractValue(C,v,0)

# Very similar to the pointer case, but since there may be additional wrappers
# hiding behind the T, we need to recursively call back into
# resolvemodifier_llvm
resolvemodifier_llvm(C, builder, t::Type{CppCast{T,To}}, v::pcpp"llvm::Value") where {T,To} =
    resolvemodifier_llvm(C,builder, T, ExtractValue(C,v,0))
resolvemodifier_llvm(C, builder, t::Type{CppDeref{T}}, v::pcpp"llvm::Value") where {T} =
    resolvemodifier_llvm(C,builder, T, ExtractValue(C,v,0))
resolvemodifier_llvm(C, builder, t::Type{CppAddr{T}}, v::pcpp"llvm::Value") where {T} =
    resolvemodifier_llvm(C,builder, T, ExtractValue(C,v,0))

function associateargs(C, builder,argt,args,pvds)
    for i = 1:length(args)
        t = stripmodifier(argt[i])
        argit = cpptype(C, t)
        if t <: CppValue
            argit = pointerTo(C,argit)
        end
        AssociateValue(C, pvds[i],argit,args[i])
    end
end
