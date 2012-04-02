--DEPS: List OutputForm runtime/ARCH/rtexns Tuple tests/TestCategory
#include "axiom.as"

import from OutputForm;
import from String;

TestTuple: TestCategory with == add {
test(): () == {
       import from Tuple Integer;
       import from Integer;
       import from SingleInteger;
       t := mktuple(Integer)(1);
       assertTrue(#t = 1);
       assertTrue(t.0 = 1);
       t := mktuple(Integer)(1,2);
       assertTrue(#t = 2::SingleInteger);
       assertTrue(t.0 = 1);
       assertTrue(t.1 = 2);
}

mktuple(X: with)(t: Tuple X): Tuple X == t;

assertTrue(b: Boolean): () == if not b then never;

}

