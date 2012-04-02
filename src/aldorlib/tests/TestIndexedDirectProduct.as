--DEPS: IndexedDirectProductObject NonNegativeInteger_OrderedAbelianMonoidSup
--DEPS: Integer_IntegralDomain tests/TestCategory
#include "axiom.as"

#pile

import from Boolean
import from IndexedDirectProductObject(Integer, NonNegativeInteger)
import from OutputForm
import from Integer
import from NonNegativeInteger

TestIndexedDirectProduct: TestCategory with
== add
 test():() ==
	 x := monomial(1,1);
	 one := monomial(1, 0);
	 assertTrue(x - x = 0)
	 assertTrue(one - one = 0)
	 assertTrue(x+one ~= x)
	 assertTrue(x = x)
	 assertTrue(one + x = x + one)
	 assertTrue(2*x = x + x)
	 assertTrue(zero?(x-x))
	 print((2*x + one)::OutputForm)

assertTrue(x: Boolean): () == if not x then never;

X: SetCategory with == Integer add;

--bar(): () ==
--       import from IndexedDirectProductObject(X, NonNegativeInteger)
--       x: IndexedDirectProductObject(X, NonNegativeInteger) := 0;