--DEPS: NonNegativeInteger_SemiRing OrderedSemiRingSegment List_StreamAggregate
--DEPS: tests/TestCategory tests/Assert
#include "axiom.as"

import from OutputForm;
import from String;

TestOrderedSemiRingSegment: TestCategory with
== add {
  NNI ==> NonNegativeInteger;
  import from Assert List NNI;
  import from List NNI;
  import from Integer;
  import from NNI;

  test(): () == {
      s: OrderedSemiRingSegment NNI := 1..(3::NNI);
      l := [x for x in s];
      assertEquals([1,2::NNI,3::NNI], l);
}
}

assertTrue(x: Boolean): () == if not x then never;
