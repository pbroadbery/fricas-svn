--DEPS: List OutputForm runtime/c/rtexns
#include "axiom.as"

import from OutputForm;
import from String;
foo(): () == {
       import from IO;
       import from List Integer;
       import from List OutputForm;
       import from OutputForm;
       import from Integer;
       print outputForm "done"
}


foo();

assertTrue(x: Boolean): () == if not x then never;
