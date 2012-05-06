#include "axiom.as"

import from Boolean;





SemiRng: Category == Join(AbelianSemiGroup, SemiGroup) with;
Rng: Category == Join(AbelianGroup,SemiRng) with;
SemiRing: Category == Join(SemiRng, AbelianMonoid, Monoid) with;

Ring: Category == Join(Rng,SemiRing,LeftModule(%), unitsKnown) with {
    --operations
      characteristic: () -> NonNegativeInteger;
        ++ characteristic() returns the characteristic of the ring
        ++ this is the smallest positive integer n such that
        ++ \spad{n*x=0} for all x in the ring, or zero if no such n
        ++ exists.
        --We can not make this a constant, since some domains are mutable
      coerce: Integer -> %;
        ++ coerce(i) converts the integer i to a member of the given domain.
--    recip: % -> Union(%,"failed") -- inherited from Monoid
   default {
      coerce(n: Integer): % == n * (1);
}
}

LeftModule(R : SemiRng) : Category == AbelianSemiGroup with {
      if R has AbelianMonoid then AbelianMonoid;
      if R has AbelianGroup then AbelianGroup;
      --operations
      *: (R,%) -> %;     ++ r*x returns the left multiplication of the module element x
                          ++ by the ring element r.
}

