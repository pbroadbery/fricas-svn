--DEPS: PseudoRemainderSequence SparseUnivariatePolynomial_UnivariatePolynomialCategory0
--DEPS: tests/TestCategory
#include "axiom.as"

#pile

import from Boolean

TestPseudoRemainderSequence: TestCategory with
== add
 test():() ==
	 import from PseudoRemainderSequence(Integer, SparseUnivariatePolynomial Integer)
	 import from Integer;
	 import from SparseUnivariatePolynomial Integer
	 import from NonNegativeInteger
	 x := monomial(1,1)
	 assertTrue(resultant(x,x) = 0)

assertTrue(x: Boolean): () == if not x then never;
