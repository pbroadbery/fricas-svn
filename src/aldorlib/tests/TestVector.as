--DEPS: Vector Integer
#include "axiom.as"

#pile

import from Boolean

foo():() == 
	 import from Vector Integer
	 import from NonNegativeInteger
	 import from Integer
	 v := new(5::NonNegativeInteger, 0);

foo();

assertTrue(x: Boolean): () == if not x then never;
