--DEPS: runtime/ARCH/rtexns tests/Assert tests/Assertions tests/TestCategory
--DEPS: Fold List_StreamAggregate UniversalSegment Integer_OrderedRing Boolean_SetCategory
#include "axiom.as"

TestFold: TestCategory with
== add {
    test(): () == {
    	    test1();
	    test2();
	    test3();
    }	
   
    test1(): () == {
    	    import from UniversalSegment Integer;
    	    import from Fold Integer;
    	    import from List Integer;
	    import from Assert Integer;
	    import from Integer;
	    for i in 1..10 repeat {
	        assertEquals(i * (i+1) quo 2, (+)/[x for x in 1..i]);
	    }
    }
    test2(): () == {
    	    import from UniversalSegment Integer;
    	    import from BooleanFoldingOperations;
    	    import from List Boolean;
	    import from Assert Boolean;
	    import from Assert Integer;
	    import from Integer;
	    import from Assertions;
	    import from List OutputForm;
	    import from OutputForm;

  	    assertTrue(_and/[true]);
	    assertFalse(_and/[false]);
	    for i in 2..16 repeat {
	        l := [bit?(i, bit) for bit in 0..(length(i) - 2)];
		assertEquals(member?(true, l), _or/l);
		assertEquals(not member?(false, l), _and/l);
	    }
     }
     test3(): () == {
	    NNI ==> NonNegativeInteger;
	    import from Assert NNI;
	    import from List NNI;
	    import from NNI;
	    import from Integer;
	    import from OutputForm;
	    import from List OutputForm;
	    import from String;
	    local count: NNI := 0;
	    xmin(n: NNI, m: NNI): NNI == { print bracket ["min"::OutputForm, n::OutputForm, m::OutputForm];free count := count + 1; min(n, m)}
	    myfold: AbsorbingFoldingTransformation NNI := folder(xmin, 0);

	    count := 0;
	    assertEquals(0, myfold/[0,0,3::NNI]);
	    assertEquals(count, 0);

	    count := 0;
	    assertEquals(0, myfold/[1,0,3::NNI]);
	    assertEquals(0, count);

	    count := 0;
	    assertEquals(0, myfold/[1,2::NNI,0]);
	    assertEquals(count, 1);
    }


}


