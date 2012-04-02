--DEPS: OutputForm Integer_SetCategory runtime/ARCH/rtexns Character_Base
--DEPS: tests/TestCategory
#include "axiom.as"

import from OutputForm;

TestInt: TestCategory == add {
   test(): () == {
      x: Integer := 1;
      y: OutputForm := coerce(x+1);
      print coerce y;
   }
}

