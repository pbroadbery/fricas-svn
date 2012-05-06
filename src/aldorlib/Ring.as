--DEPS:  Rng SemiRing LeftModule unitsKnown NonNegativeInteger Integer
#include "axiom.as"

import from Boolean;

Ring: Category == with {
     	Rng; SemiRing; unitsKnown; LeftModule %; 
     1: %; 
     *: (Integer, %) -> %;
    --operations
      characteristic: () -> NonNegativeInteger;
        ++ characteristic() returns the characteristic of the ring
        ++ this is the smallest positive integer n such that
        ++ \spad{n*x=0} for all x in the ring, or zero if no such n
        ++ exists.
        --We can not make this a constant, since some domains are mutable
      coerce: Integer -> %;
        ++ coerce(i) converts the integer i to a member of the given domain.
--    recip: % -> Partial(%) -- inherited from Monoid
   default {
      coerce(n: Integer): % == { f: (Integer, %) -> % := *; f(n, 1)}
}
}
