#include "axiom.as"

import from Boolean;

extend Equation(R: SetCategory): with {
   =: (R, R) -> %;
}
== add {
   Rep ==> Record(lhs: R, rhs: R);
   import from Rep;
   
   (a: R) = (b: R): % == per [a, b]
}
