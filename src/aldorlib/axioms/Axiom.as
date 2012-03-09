--DEPS: lang init_Boolean init_String axioms/AxiomEnv
#include "axiom.as"

Axiom: with {
  name: % -> String;
  evaluate: (%, AxiomEnv) -> Boolean;
  axiom: (String, AxiomEnv -> Boolean) -> %;
}
== add {
   Rep ==> Record(name: String, fn: AxiomEnv -> Boolean);
   import from Rep;

   axiom(name: String, f: AxiomEnv -> Boolean): % == per [name, f];

   name(a: %): String == rep(a).name;
   evaluate(x: %, env: AxiomEnv): Boolean == (rep(x).fn)(env)
}

