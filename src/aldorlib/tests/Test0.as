--DEPS: SparseUnivariatePolynomial_UnivariatePolynomialCategory

#include "axiom.as"

#pile
import from SparseUnivariatePolynomial Integer;
import from Integer;
import from NonNegativeInteger;
import from OutputForm;

foo(): () == 
   one := monomial(1, 0)
   print coerce(one+one)
   x := monomial(1, 1)
   print coerce(x+one)
   print coerce((x+1)^(5::NonNegativeInteger))

foo();
