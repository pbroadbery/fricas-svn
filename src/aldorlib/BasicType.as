#include "axiom"

BasicType: Category == with {
      =: (%,%) -> Boolean;    ++ x=y tests if x and y are equal.
      ~=: (%,%) -> Boolean;   ++ x~=y tests if x and y are not equal.
   default {
      (x:%) ~= (y:%): Boolean == not(x=y);
}}

