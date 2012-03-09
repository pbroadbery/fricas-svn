--DEPS: SparseUnivariatePolynomial_FiniteAbelianMonoidRing
#include "axiom.as"


#pile

import from Boolean
import from SparseUnivariatePolynomial(Integer)
import from OutputForm
import from Integer
import from NonNegativeInteger

foo():() == 
	 x := monomial(1,1);
	 assertTrue(degree x = 1)
	 assertTrue(x+1 ~= x)
	 assertTrue(x = x)
	 assertTrue(1 + x = x + 1)
	 assertTrue(2*x = x + x)
	 assertTrue((x+1)*(x+1) = x*x + 2*x + 1)
	 print(x::OutputForm)
	 print(((x+1)*(x+1))::OutputForm)

foo();

assertTrue(x: Boolean): () == if not x then never;
