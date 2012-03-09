--DEPS: OutputForm Integer_SetCategory runtime/c/rtexns Character_Base
#include "axiom.as"

import from OutputForm;

foo(): () == {
   x: Integer := 1;
   y: OutputForm := coerce(x+1);
   print coerce y;
}


foo();