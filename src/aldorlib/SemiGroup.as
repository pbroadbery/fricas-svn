--DEPS:  SetCategory init_PositiveInteger RepeatedSquaring
#include "axiom.as"

import from Boolean;

SemiGroup: Category == SetCategory with {
    --operations
      *: (%,%) -> %;                  ++ x*y returns the product of x and y.
      ^: (%,PositiveInteger) -> %;
          ++ x^n returns the repeated product
          ++ of x n times, i.e. exponentiation.
    default {
      import from RepeatedSquaring(%);
      (x:%) ^ (n:PositiveInteger): % == expt(x,n);
}}


