--DEPS: lang init_Boolean init_String axioms/RandomGenerator
#include "axiom.as"

AxiomEnv: with {
   new: RandomGenerator -> %;
   random: % -> RandomGenerator;
}
== add {
   Rep ==> RandomGenerator;

   new(r: RandomGenerator): % == per r;
   random(x: %): RandomGenerator == rep x;
}
