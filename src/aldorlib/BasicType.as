--DEPS:  lang init_Boolean
#include "axiom"

BasicType: Category == with {
      =: (%,%) -> Boolean;    ++ x=y tests if x and y are equal.
      ~=: (%,%) -> Boolean;   ++ x~=y tests if x and y are not equal.
   default {
      (x:%) ~= (y:%): Boolean == not(x=y);
  }
--  axioms {
--      default a, b: %
--      equality(a, b): Boolean == not (a = b) = (a ~= b)
--      eqcommutative(a, b): Boolean == (a = b) = (b = a)
--  }

}

