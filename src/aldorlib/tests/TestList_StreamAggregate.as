--DEPS: List_StreamAggregate OutputForm runtime/ARCH/rtexns
--DEPS: NonNegativeInteger_OrderedAbelianMonoidSup 
--DEPS: tests/Assert tests/Assertions tests/TestCategory

#include "axiom.as"

import from OutputForm;
import from String;

TestList_StreamAggregate: TestCategory with 
== add {
test(): () == {
       import from Assertions;
       import from Assert List Integer;
       import from Assert Integer;
       import from Assert NonNegativeInteger;
       import from List Integer;
       import from Integer;
       import from NonNegativeInteger;
       import from OutputForm;

       l: List Integer := empty();
       assertTrue(empty? l);

       l := [];
       l := concat!(l, 4);

       assertEquals(#l, 1);
       assertEquals(first l, 4);

       l := [1];
       concat!(l, 2);

       assertEquals(2::NonNegativeInteger, #l);
       assertEquals(2, second l);

       assertEquals([], insert([], [], 1));
       assertEquals([1], insert([], [1], 1));

       assertEquals([10, 1], insert([10], [1], 1));
       assertEquals([1, 10], insert([10], [1], 2));

       assertEquals([10, 1,2], insert([10], [1,2], 1));
       assertEquals([1,10, 2], insert([10], [1,2], 2));
       assertEquals([1,2, 10], insert([10], [1,2], 3));

       assertTrue(Integer has SetCategory);
       import from SExpression;
       l: List Integer := [1,2,3];
       outform := l::OutputForm;
       print outputForm unparse(outform pretend SExpression);
}


}

