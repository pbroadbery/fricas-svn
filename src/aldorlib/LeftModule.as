--DEPS:  SemiRng AbelianSemiGroup AbelianMonoid AbelianGroup
#include "axiom.as"

import from Boolean;

LeftModule(R : SemiRng) : Category == AbelianSemiGroup with {
      if R has AbelianMonoid then AbelianMonoid;
      if R has AbelianGroup then AbelianGroup;
      --operations
      *: (R,%) -> %;     ++ r*x returns the left multiplication of the module element x
                          ++ by the ring element r.
}

