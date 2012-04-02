--DEPS: PolynomialRing NonNegativeInteger_OrderedAbelianMonoidSup
--DEPS: tests/TestCategory

#include "axiom.as"

#pile

import from Boolean
import from PolynomialRing(Integer, NonNegativeInteger)
import from OutputForm
import from Integer
import from NonNegativeInteger

TestPolynomialRing: TestCategory with
== add
  test(): () ==
	 x := monomial(1,1);
	 one := monomial(1, 0);
	 assertTrue(one * one = one)
	 assertTrue((x+1)*(x+1) = x*x + 2*x + 1)
	 assertTrue(x - x = 0)
	 assertTrue(one - one = 0)
	 assertTrue(degree x = 1)
	 assertTrue(x+1 ~= x)
	 assertTrue(x = x)
	 assertTrue(1 + x = x + 1)
	 assertTrue(2*x = x + x)
	 print((2*x + 1)::OutputForm)
	 print(x::OutputForm)
	 print(((x+1)*(x+1)*(x+1))::OutputForm)

assertTrue(x: Boolean): () == if not x then never;
