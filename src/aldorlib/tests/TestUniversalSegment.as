--DEPS: List OutputForm UniversalSegment runtime/ARCH/rtexns Integer_OrderedRing
--DEPS: tests/TestCategory
#include "axiom.as"

import from OutputForm;
import from String;

TestUniversalSegment: TestCategory with
== add {
  test(): () == {
       import from IO;
       import from List Integer;
       import from UniversalSegment Integer;
       import from Integer;
       import from NonNegativeInteger;
       s := 1..2;
       assertTrue(lo s = 1);
       assertTrue(hi s = 2);
       a := [x for x in 1..2];
       assertTrue(first a = 1);
       assertTrue(first rest a = 2);
       assertTrue(#a = 2::NonNegativeInteger);
--       assertTrue([x for x in 1..2] = [1,2]);
       "done"
}
}

assertTrue(x: Boolean): () == if not x then never;
