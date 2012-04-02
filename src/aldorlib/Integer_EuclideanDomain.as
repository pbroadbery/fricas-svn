--DEPS: Integer_IntegralDomain EuclideanDomain
#include "axiom"

import from System;
import from String;
import from Boolean;
#pile

extend Integer: EuclideanDomain with 
== add
   euclideanSize(n: %): NonNegativeInteger == coerce abs(n)
   divide(a: %, b: %): Record(quotient: %, remainder: %) == [divide(a, b)]