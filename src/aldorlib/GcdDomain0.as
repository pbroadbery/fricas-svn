#include "axiom.as"

import from System;
import from String;
import from Boolean;
       
GcdDomain0: Category == IntegralDomain with {
    --operations
      gcd: (%,%) -> %;
            ++ gcd(x,y) returns the greatest common divisor of x and y.
            -- gcd(x,y) = gcd(y,x) in the presence of canonicalUnitNormal,
            -- but not necessarily elsewhere
      gcd: List(%) -> %;
            ++ gcd(l) returns the common gcd of the elements in the list l.
      lcm: (%,%) -> %;
            ++ lcm(x,y) returns the least common multiple of x and y.
            -- lcm(x,y) = lcm(y,x) in the presence of canonicalUnitNormal,
            -- but not necessarily elsewhere
      lcm: List(%) -> %;
            ++ lcm(l) returns the least common multiple of the elements of the list l.
    default {
      import from Partial %;
      lcm(x: %,y: %): % == {
        y = 0 => 0;
        x = 0 => 0;
        LCM : Partial(%) := exquo(y, gcd(x,y));
        success? LCM =>  x * value(LCM);
        error "bad gcd in lcm computation"
      }
      lcm(l:List %): % == reduce(lcm,l,1,0);
      gcd(l:List %): % == reduce(gcd,l,0,1);
      SUP ==> SparseUnivariatePolynomial;
}
}