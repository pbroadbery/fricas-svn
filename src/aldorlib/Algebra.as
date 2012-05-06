#include "axiom"

import from Boolean;

Algebra(X:CommutativeRing): Category ==
  Join(Ring, Module X) with {
    --operations
      coerce: X -> %;
          ++ coerce(r) maps the ring element r to a member of the algebra.
 default {
  coerce(x:X):% == { f: (X,%) -> % := *; f(x,1)}
}
}
