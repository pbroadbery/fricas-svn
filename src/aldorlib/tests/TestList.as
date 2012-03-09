--DEPS: List OutputForm runtime/c/rtexns NonNegativeInteger runtime/c/Local 
#include "axiom.as"

import from OutputForm;
import from String;


local assertTrue(x: Boolean): () == if not x then never;
local assertEquals(n: NonNegativeInteger, n2: NonNegativeInteger): () == if n ~= n2 then never;
local assertEquals(n: Integer, n2: Integer): () == if n ~= n2 then never;

foo(): () == {
       import from IO;
       import from List Integer;
       import from List OutputForm;
       import from OutputForm;
       import from Integer;
       import from NonNegativeInteger;
       l: List Integer := empty();
       not empty? l => never;
       l := cons(1, l);
       print outputForm "FIRST";
       print outputForm first l;
       print outputForm "CHECK";
       first l ~= 1 => never;
       empty? l => never;
       not empty? rest l => never;
       print outputForm "LLLL first/second";
       x := cons(1, cons(2, empty()));
       y := cons(10, empty());
       print outputForm "(CHECK first/second";
       assertTrue(empty? rest y);
       assertTrue(not empty? y);
       assertTrue(first x = 1);
       assertTrue(second x = 2);
       assertTrue(first y = 10);
       print outputForm "DONE)";
       x.rest := y;
       assertTrue(first x = 1);
       assertTrue(second x = 10);
       print outputForm "[1,2,3]";
       l := [1,2,3];
       assertTrue(first l = 1);
       assertTrue(second l = 2);
       assertTrue(#l = 3::NonNegativeInteger);
       l := [];
       assertEquals(#l, 0);
       forms := [outputForm aa for aa in l];
       print bracket forms;

       l := [];
       assertTrue(empty? reverse! l);
       l := [1];
       l := reverse! l;
       assertEquals(1, coerce #l);
       assertEquals(1, first l);

       l := [1, 2];
       l := reverse! l;
       assertEquals(2, coerce #l);
       assertEquals(2, first l);
       assertEquals(1, second l);

       l := [1,2,3];
       l := reverse! l;
       assertEquals(3, coerce #l);
       assertEquals(3, first l);
       assertEquals(2, second l);
       assertEquals(1, first rest rest l);

       l := [1,2,3];
       assertEquals(3, last l);
       l := [1];
       assertEquals(1, last l);
}


foo2(): () == {
       import from List Integer;
       import from Integer;
       assertTrue(empty? reverse empty());
       assertTrue(first reverse [1,2,3] = 3);
       assertTrue(second reverse [1,2,3] = 2);
       l := [1,2,3,4,5,6];
       assertTrue(reverse reverse l = l);
}

foo2();
foo();
