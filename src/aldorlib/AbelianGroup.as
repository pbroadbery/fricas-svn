--DEPS:  CancellationAbelianMonoid 
#include "axiom.as"

import from Boolean;

#pile

AbelianGroup: Category == CancellationAbelianMonoid with
    --operations
    -: % -> %                      ++ -x is the additive inverse of x.
    -: (%,%) -> %                  ++ x-y is the difference of x and y
                                       ++ i.e. \spad{x + (-y)}.
                       -- subsumes the partial subtraction from previous
    *: (Integer,%) -> %            ++ n*x is the product of x by the integer n.
    default
      (x:%) - (y:%): % == x+(-y)
      subtractIfCan(x:%, y:%): Partial % == success(x-y)
      (n:NonNegativeInteger) * (x:%): % == (n::Integer) * x

      import from RepeatedDoubling(%)
      (n:Integer) * (x:%): % ==
          zero? n => 0
          n>0 => double(n pretend PositiveInteger,x)
          double((-n) pretend PositiveInteger,-x)

