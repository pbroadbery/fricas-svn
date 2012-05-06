--DEPS: Ring  DifferentialRing Symbol_SetCategory PartialDifferentialRing
#include "axiom.as"

import from Boolean;

DifferentialExtension(R:Ring): Category == Ring with {
    --operations
    differentiate: (%, R -> R) -> %;
       ++ differentiate(x, deriv) differentiates x extending
       ++ the derivation deriv on R.
    differentiate: (%, R -> R, NonNegativeInteger) -> %;
       ++ differentiate(x, deriv, n) differentiate x n times
       ++ using a derivation which extends deriv on R.
    D: (%, R -> R) -> %;
       ++ D(x, deriv) differentiates x extending
       ++ the derivation deriv on R.
    D: (%, R -> R, NonNegativeInteger) -> %;
       ++ D(x, deriv, n) differentiate x n times
       ++ using a derivation which extends deriv on R.
    if R has DifferentialRing then DifferentialRing;
    if R has PartialDifferentialRing(Symbol) then
             PartialDifferentialRing(Symbol);
  default {
    default x: %;
    differentiate(x:%, derivation: R -> R, n:NonNegativeInteger):% =={
      import from Segment NonNegativeInteger;
      for i in 1..n repeat x := differentiate(x, derivation);
      x}
    D(x:%, derivation: R -> R): % == differentiate(x, derivation);
    D(x:%, derivation: R -> R, n:NonNegativeInteger): % ==
            differentiate(x, derivation, n);

    if R has DifferentialRing then
      differentiate x: % == differentiate(x, differentiate$R);

    if R has PartialDifferentialRing Symbol then {
      differentiate(x:%, v:Symbol):% == 
        differentiate(x, (s : R) : R +-> differentiate(s, v)$R);
    }
}}
