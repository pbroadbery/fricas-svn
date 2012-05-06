--DEPS:  SemiRng AbelianSemiGroup AbelianMonoid AbelianGroup
#include "axiom"

import from Boolean;

RightModule(R : SemiRng) : Category == AbelianSemiGroup with {
      if R has AbelianMonoid then AbelianMonoid;
      if R has AbelianGroup then AbelianGroup;
      --operations
      *: (%,R) -> %  ++ x*r returns the right multiplication of the module element x
                       ++ by the ring element r.
}