--DEPS: SparseUnivariatePolynomial_UnivariatePolynomialCategory
--DEPS: tests/TestCategory tests/Assert
#include "axiom.as"

#pile
import from SparseUnivariatePolynomial Integer;
import from Integer;
import from NonNegativeInteger;
import from OutputForm;
import from String
import from Assert SparseUnivariatePolynomial Integer

TestP0: TestCategory with
== add
 test(): () ==
   import from Symbol
   one := monomial(1, 0)
   print coerce(one+one)
   x := monomial(1, 1)
   assertEquals(x, one * x)
   print coerce(x+one)
   print coerce((x+1)^(5::NonNegativeInteger))

   q: OutputForm := outputForm(#"q")
   print outputForm((x+1)^(5::NonNegativeInteger), q);
   
