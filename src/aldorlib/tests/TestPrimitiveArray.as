--DEPS: PrimitiveArray Integer NonNegativeInteger_OrderedAbelianMonoidSup
#include "axiom.as"

#pile

import from Boolean

foo():() == 
	 import from PrimitiveArray String
	 import from NonNegativeInteger
	 import from String
	 import from Integer;
	 import from IO
	 v := new(5::NonNegativeInteger, "zz");
	 print ("v.0: " pretend LString); print (v.1 pretend LString);
	 assertTrue(v.0 = "zz");
	 assertTrue(#v = 5::NonNegativeInteger);
	 v.0 := "aa";
	 assertTrue(v.0 = "aa");

foo();

assertTrue(x: Boolean): () == if not x then never;
