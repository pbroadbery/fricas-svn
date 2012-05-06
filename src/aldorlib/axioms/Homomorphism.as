--DEPS: axioms/Axiom axioms/Stream
#include "axiom.as"

Homomorphism(R1: Ring, R2: Ring): HomomorphismCategory with {
   new: (R1 -> R2) -> %;
}
== add {
   Rep ==> R1 -> R2;
   new(f: R1 -> R2): % == per f;
   apply(h: %, r: R1): R2 == rep(h)(r);
   kernel(h: %, r: R1): Boolean == zero? h r;
}
