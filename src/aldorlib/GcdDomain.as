#include "axiom.as"

import from System;
import from String;
import from Boolean;
       
GcdDomain: Category == GcdDomain0 with {
      gcdPolynomial: (SparseUnivariatePolynomial %, SparseUnivariatePolynomial %) ->
           SparseUnivariatePolynomial %;
            ++ gcdPolynomial(p,q) returns the greatest common divisor (gcd) of
            ++ univariate polynomials over the domain
}
}