--DEPS:  lang init_Boolean Integer AbelianSemiGroup AbelianMonoid CancellationAbelianMonoid 
#include "axiom.as"

import from Boolean;

--AbelianSemiGroup: Category == with {
--      +: (%,%) -> % ;                 ++ x+y computes the sum of x and y.
--}

--AbelianMonoid: Category == AbelianSemiGroup with {
--    --operations
--      0: %;
--        ++ 0 is the additive identity element.
--      sample: () -> %;
--        ++ sample yields a value of type %
--      zero?: % -> Boolean;
--}

--CancellationAbelianMonoid: Category == AbelianMonoid with {
--    --operations
--      subtractIfCan: (%,%) -> Union(%,'failed')
--}

--AbelianGroup: Category == CancellationAbelianMonoid with {
--      -: % -> %;                      ++ -x is the additive inverse of x.
--      -: (%,%) -> %;                  ++ x-y is the difference of x and y
--                                       ++ i.e. \spad{x + (-y)}.
--                       -- subsumes the partial subtraction from previous
--      *: (Integer,%) -> %;            ++ n*x is the product of x by the integer n.
--}

AbelianGroup: Category == CancellationAbelianMonoid with {
      -: % -> %;                      ++ -x is the additive inverse of x.
      -: (%,%) -> %;                  ++ x-y is the difference of x and y
                                       ++ i.e. \spad{x + (-y)}.
                       -- subsumes the partial subtraction from previous
      *: (Integer,%) -> %;            ++ n*x is the product of x by the integer n.
      default {
--            (x:%) - (y:%):% == x+(-y);
	    subtractIfCan(x:%, y:%):Union(x: %, y: 'failed') == never;
--	    (n:NonNegativeInteger) * (x:%): % == (n::Integer) * x;
--	    (n:Integer) * (x:%): % == never;
}
}

Rng: Category == AbelianGroup with { -- & SemiRng
     foo: Integer -> %;
     0: %;
     default { foo(n: Integer): % == { n * 0 }}
}
