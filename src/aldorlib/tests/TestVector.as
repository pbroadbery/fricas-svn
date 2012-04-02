--DEPS: Vector Integer tests/TestCategory
#include "axiom.as"

#pile

import from Boolean

TestVector: TestCategory
== add
  test():() ==
	 import from Vector Integer
	 import from NonNegativeInteger
	 import from Integer
	 v := new(5::NonNegativeInteger, 0);

assertTrue(x: Boolean): () == if not x then never;
