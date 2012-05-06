#include "axiom"

import from Boolean;

PartialOrder: Category == with {
    <: (%,%) -> Boolean;
      ++ x < y is a less than test.
    >:         (%, %) -> Boolean;
      ++ x > y is a greater than test.
    >=:        (%, %) -> Boolean;
      ++ x >= y is a greater than or equal test.
    <=:        (%, %) -> Boolean;
      ++ x <= y is a less than or equal test.

  default {
     default x, y: %;
     x >= y: Boolean == y <= x;
     x > y: Boolean == y < x;

     x < y: Boolean == x <= y and not(y <= x);
}
}
