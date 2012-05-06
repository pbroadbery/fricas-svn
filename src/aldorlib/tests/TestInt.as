--DEPS: OutputForm Integer_SetCategory runtime/ARCH/rtexns Character_Base
--DEPS: tests/TestCategory tests/Assert Integer Boolean_SetCategory
#include "axiom.as"

import from OutputForm;

TestInt: TestCategory == add {
   test(): () == {
      import from Assert Integer;
      import from Assert Boolean;
      import from List OutputForm;
      import from Integer;
      x: Integer := 1;
      y: OutputForm := coerce(x+1);
      print coerce y;
      assertEquals(1, length(0));
      assertEquals(1, length(1));
      assertEquals(2, length(2));
      assertEquals(2, length(3));
      assertEquals(3, length(4));
      i: Integer := 0;
      while i < 10 repeat {
         bit: Integer := 1;
         while bit <= length i repeat {
	    assertEquals(odd? shift(i, -bit), bit?(i, bit));
	    bit := bit + 1;
	 }
	 i := i+1;
      }
   }
}

