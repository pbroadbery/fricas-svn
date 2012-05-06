#include "axiom.as"

import from Boolean;

AbelianSemiGroup: Category == SetCategory with {
      +: (%,%) -> % ;                 ++ x+y computes the sum of x and y.
      *: (PositiveInteger,%) -> %;
        ++ n*x computes the left-multiplication of x by the positive integer n.
        ++ This is equivalent to adding x to itself n times.
    default {
      import from RepeatedDoubling(%);
        (n:PositiveInteger) * (x:%): % == double(n,x)
}
}

