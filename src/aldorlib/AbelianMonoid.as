--DEPS:  AbelianSemiGroup NonNegativeInteger PositiveInteger
#include "axiom.as"

import from Boolean;

AbelianMonoid: Category == AbelianSemiGroup with {
    --operations
      0: %;
        ++ 0 is the additive identity element.
      sample: () -> %;
        ++ sample yields a value of type %
      zero?: % -> Boolean;
        ++ zero?(x) tests if x is equal to 0.
      *: (NonNegativeInteger,%) -> %;
        ++ n * x is left-multiplication by a non negative integer
    default {
      import from RepeatedDoubling(%);
      zero?(x: %): Boolean == x = 0;
      (n:PositiveInteger) * (x:%): % == (n::NonNegativeInteger) * x;
      sample(): % == 0;
        (n:NonNegativeInteger) * (x:%): % == {
          zero? n => 0;
          double(n pretend PositiveInteger,x)
     
}
}
}

