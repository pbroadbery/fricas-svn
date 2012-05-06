--DEPS:  init_Equation SetCategory CoercibleTo OutputForm
#include "axiom.as"

import from Boolean;

extend Equation(R: SetCategory): with {
   if R has SetCategory then SetCategory;
   if R has SetCategory then CoercibleTo Boolean;
   
   =: (R, R) -> %;
   lhs: % -> R;
   rhs: % -> R;
}
== add {
   Ex ==> OutputForm;
   Rep ==> Record(lhs: R, rhs: R);
   import from Rep;
   
   (a: R) = (b: R): % == per [a, b];
   lhs(e: %): R == rep(e).lhs;
   rhs(e: %): R == rep(e).rhs;
   
   if R has SetCategory then {
        (eq1: %) = (eq2: %): Boolean == (lhs eq1 = lhs eq2)@Boolean and (rhs eq1 = rhs eq2)@Boolean;
        coerce(eqn:%):Boolean == lhs eqn = rhs eqn;
        coerce(eqn:%):Ex == (lhs eqn)::Ex = (rhs eqn)::Ex;
   }
}
