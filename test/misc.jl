# Issue 37 - Assertion failure when calling function declared `extern "C"`
cxx"""
extern "C" {
    void foo37() {
    }
}
"""
@cxx foo37()

# Constnes in template arguments - issue #33
cxx"""
#include <map>
#include <string>

typedef std::map<std::string, std::string> Map;

Map getMap()
{
    return Map({ {"hello", "world"}, {"everything", "awesome"} });
}
int dumpMap(Map m)
{
    return 1;
}
"""
m = @cxx getMap()
@test (@cxx dumpMap(m)) == 1

# Reference return (#50)
cxx"""
int x50 = 6;
int &bar50(int *foo) {
    return *foo;
}
"""
@cxx bar50(@cxx &x50)

# Global Initializers (#53)
cxx"""
#include <vector>

std::vector<int> v(10);
"""
@test icxx"v.size();" == 10

# References to functions (#51)
cxx"""
void foo51() {}
"""

@test_throws ErrorException (@cxx foo51)
@test isa((@cxx &foo51),CppFptr)

# References to member functions (#55)
cxx"""
class foo55 {
    foo55() {};
public:
    void bar() {};
};
"""
@test isa((@cxx &foo55::bar),CppMFptr)
