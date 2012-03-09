--DEPS: axioms/Axiom axioms/Stream
#include "axiom.as"

AxiomConstructorPackage(T: Type): with {
  	axiom: (String, (T, T) -> Boolean, AxiomEnv -> Stream(Cross(T, T))) -> Axiom;
} == add {
  import from Stream Cross(T, T);
  import from Axiom;

  axiom(name: String, f: (T, T) -> Boolean, stream: AxiomEnv -> Stream(Cross(T, T))): Axiom == {
	axiom(name, (env: AxiomEnv): Boolean +-> test(f, stream(env)))
  }

  local test(f: (T, T) -> Boolean, s: Stream Cross(T, T)): Boolean == {
     for (a, b) in s repeat 
        if not f(a, b) then return false;
     return true;
  }
}

