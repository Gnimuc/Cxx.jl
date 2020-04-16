"""
Clang's QualType. A QualType is a pointer to a clang class object that
contains the information about the actual type, as well as storing the CVR
qualifiers in the unused bits of the pointer. Here we just treat QualType
as an opaque struct with one pointer-sized member.
"""
struct QualType
    ptr::Ptr{Cvoid}
end
Base.convert(::Type{Ptr{Cvoid}}, QT::QualType) = QT.ptr

# All types that are recgonized as builtins
const CxxBuiltinTypes = Union{Type{Bool},
    Type{UInt8},  Type{Int8},    Type{UInt16}, Type{Int16},
    Type{Int32},  Type{UInt32},  Type{Int64},  Type{UInt64},
    Type{Float32}, Type{Float64}}
const CxxBuiltinTs = Union{Bool, UInt8, Int8, UInt16, Int16,
    Int32, UInt32, Int64, UInt64, Float32, Float64}

# # # Representing C++ values
#
# Since we can't always keep C++ values in C++ land and to make C++ values
# convenient to work with, we need to come up with a way to represent them in
# Julia. In particular, we would like to be able to represent both C++ types
# has well as having a way to represent runtime instances of C++ values.
#
# One way to do this would be to have a
#
# struct CppObject{ClangType}
#     data::Ptr{Cvoid}
# end
#
# where ClangType is simply a pointer to Clang's in memory representation. This
# has the advantage that working with this type does not introduce a separate
# name lookup whenever it is used. However, it also has the disadvantage that
# it is not stable across serialization and not very meaningful.
#
# Instead, what we do here is build up a hierarchy of Julia types that represent
# the C++ type hierarchy. This has the advantage that clang does not necessarily
# need to be in memory to work with these object, as well as allowing these
# types to be stable across serialization. However, it comes with the disadvantage
# of having to perform a name lookup to get the clang::Type* pointer back.
#
# In the future, we may want to have a cache that maps types to clang types,
# or go with a different model entirely, but that decision should be based
# on experience how these behave in practice.
#
# # A note on CVR qualifiers
#
# Though I had hoped to avoid it, correctly representing template parameters
# requires tracking CVR (const, volatile, restrict) qualifiers on types. The way
# this is currently implemented is as an extra CVR type parameter on
# applicable julia types. This type parameter should be a tuple of Bools
# indicating whether the qualifier is present in CVR order.
#
import Base: cconvert
export @cpcpp_str, @pcpp_str, @vcpp_str, @rcpp_str

"""
    struct CppBaseType{s}
Represents a base C++ type, i.e. a type that is not a **pointer**, a **reference** or a **template**.
`s` is a symbol of the types fully qualified name, e.g. `int`, `char` or `foo::bar`.
It is usually used directly as a type, rather than as an instance.
"""
struct CppBaseType{s} end

"""
    struct CppTemplate{T,targs}
A templated type where `T` is the [`CppBaseType`](@ref) to be templated and
`targs` is a tuple of template arguments.
"""
struct CppTemplate{T,targs} end

"""
    struct CxxQualType{T,CVR}
A base type with extra CVR qualifications
"""
struct CxxQualType{T,CVR} end

"""
    struct CxxArrayType{T}
The abstract notion of a C++ array type
"""
struct CxxArrayType{T} end

"""
    mutable struct CppValue{T,N}
The equivalent of a C++ on-stack value. `T` is a [`CppBaseType`](@ref) or a [`CppTemplate`](@ref).
"""
mutable struct CppValue{T,N}
    data::NTuple{N,UInt8}
    CppValue{T,N}(data::NTuple{N,UInt8}) where {T,N} = new{T,N}(data)
    CppValue{T,N}() where {T,N} = new{T,N}()
end

"""
    primitive type CppRef{T,CVR}
The equivalent of a C++ reference.
`T` can be any valid C++ type other than [`CppRef`](@ref).
"""
primitive type CppRef{T,CVR} 8*sizeof(Ptr{Cvoid}) end
CppRef{T,CVR}(p::Ptr{Cvoid}) where {T,CVR} = reinterpret(CppRef{T,CVR}, p)

Base.cconvert(::Type{Ptr{Cvoid}}, p::CppRef) = reinterpret(Ptr{Cvoid}, p)
Base.unsafe_load(p::CppRef{T}) where {T<:Union{CxxBuiltinTs,Ptr}} = unsafe_load(reinterpret(Ptr{T}, p))
Base.convert(::Type{T}, p::CppRef{T}) where {T<:CxxBuiltinTs} = unsafe_load(p)

"""
    primitive type CppPtr{T,CVR}
The equivalent of a C++ pointer.
`T` can be a [`CppValue`](@ref), [`CppPtr`](@ref), etc. depending on the pointed to type,
but is never a [`CppBaseType`](@ref) or [`CppTemplate`](@ref) directly.
# TODO: Maybe use Ptr{CppValue} and Ptr{CppFunc} instead?
# struct CppPtr{T,CVR}
#     ptr::Ptr{Cvoid}
# end
# Make CppPtr and Ptr the same in the julia calling convention
"""
primitive type CppPtr{T,CVR} 8*sizeof(Ptr{Cvoid}) end
CppPtr{T,CVR}(p::Ptr{Cvoid}) where {T,CVR} = reinterpret(CppPtr{T,CVR}, p)

Base.cconvert(::Type{Ptr{Cvoid}}, p::CppPtr) = reinterpret(Ptr{Cvoid}, p)
Base.convert(::Type{Int}, p::CppPtr) = convert(Int,reinterpret(Ptr{Cvoid}, p))
Base.convert(::Type{UInt}, p::CppPtr) = convert(UInt,reinterpret(Ptr{Cvoid}, p))
Base.convert(::Type{Ptr{Cvoid}}, p::CppPtr) = reinterpret(Ptr{Cvoid}, p)

Base.:(==)(p1::CppPtr, p2::Ptr) = convert(Ptr{Cvoid}, p1) == p2
Base.:(==)(p1::Ptr, p2::CppPtr) = p1 == convert(Ptr{Cvoid}, p2)

Base.unsafe_load(p::CppRef{T}) where {T<:CppPtr} = unsafe_load(reinterpret(Ptr{T}, p))

"""
    struct CppFunc{rt,argt}
Provides a common type for [`CppFptr`](@ref).
"""
struct CppFunc{rt,argt} end

"""
    struct CppFptr{func}
The equivalent of a C++ `rt (*foo)(argt...)`.
"""
struct CppFptr{func}
    ptr::Ptr{Cvoid}
end

"""
    struct CppEnum{S,T}
Represent a C/C++ Enum.
`S` is a symbol, representing the fully qualified nameof the enum.
`T` the underlying type.
"""
struct CppEnum{S,T}
    val::T
end
Base.:(==)(p1::CppEnum, p2::Integer) = p1.val == p2
Base.:(==)(p1::Integer, p2::CppEnum) = p1 == p2.val

Base.unsafe_load(p::CppRef{T}) where {T<:CppEnum} = unsafe_load(reinterpret(Ptr{Cint}, p))

# Convenience string literals for the above - part of the user facing
# functionality. Due to the complexity of the representation hierarchy,
# it is convenient to have these string macros, for the common case where
# a user simply wants to refer to a type but does not care about CVR qualifiers
# etc.

const NullCVR = (false,false,false)

"""
    pcpp"typename"
Convenience string literals for constructing a null CVR C++ pointer([`CppPtr`](@ref)).
"""
macro pcpp_str(typename)
    name = Symbol(typename)
    CppPtr{
        CxxQualType{
            CppBaseType{name},
            NullCVR
        },
        NullCVR
    }
end

"""
    cpcpp"typename"
Convenience string literals for constructing a constant C++ pointer([`CppPtr`](@ref)).
"""
macro cpcpp_str(typename)
    name = Symbol(typename)
    CppPtr{
        CxxQualType{
            CppBaseType{name},
            (true,false,false)
        },
        NullCVR
    }
end

"""
    rcpp"typename"
Convenience string literals for constructing a C++ reference([`CppRef`](@ref)).
"""
macro rcpp_str(typename)
    name = Symbol(typename)
    CppRef{
        CppBaseType{name},
        NullCVR
    }
end

"""
    vcpp"typename"
Convenience string literals for constructing a C++ on-stack value([`CppValue`](@ref)).
"""
macro vcpp_str(typename)
    name = Symbol(typename)
    CppValue{
        CxxQualType{
            CppBaseType{name},
            NullCVR
        }
    }
end

pcpp(x::Type{CppValue{T,N}}) where {T,N} = CppPtr{T,NullCVR}
pcpp(x::Type{CppValue{T}}) where {T} = CppPtr{T,NullCVR}

# Convert C++ QualType representation to julia representation
QualType(T::vcpp"clang::QualType") = reinterpret(QualType, [T.data])[]
