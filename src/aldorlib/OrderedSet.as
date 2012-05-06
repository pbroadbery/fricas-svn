--DEPS:  Comparable PartialOrder 
#include "axiom"

import from Boolean;

OrderedSet: Category == Join(Comparable, PartialOrder) with {
  --operations

    max: (%,%) -> %;
      ++ max(x,y) returns the maximum of x and y relative to "<".
    min: (%,%) -> %;
      ++ min(x,y) returns the minimum of x and y relative to "<".
  default {
  --declarations
    default x,y: %;
    -- transitional definitions
    smaller?(x, y): Boolean == x < y;

  --definitions
  -- These really ought to become some sort of macro
    max(x,y): % == {
      x > y => x;
      y}
    min(x,y): % == {
      x > y => y;
      x}
    ((x: %) >  (y: %)) : Boolean == y < x;
    ((x: %) >= (y: %)) : Boolean == not (x < y);
    ((x: %) <= (y: %)) : Boolean == not (y < x);


}
}