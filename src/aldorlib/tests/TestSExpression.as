--DEPS: List OutputForm runtime/ARCH/SExpression Tuple DoubleFloat String_SetCategory 
--DEPS: runtime/ARCH/rtexns Integer_SetCategory tests/TestCategory tests/Assert 
#include "axiom.as"

import from OutputForm;
import from String;
import from Integer;
import from Symbol;
import from DoubleFloat;

TestSExpression: TestCategory with
== add {

test(): () == {
       import from Assert Integer;
       local sx: SExpression;
       sx := nil;
       assertTrue(null? sx);
       assertFalse(integer? sx);
       assertFalse(string? sx);
       assertFalse(symbol? sx);
       assertFalse(float? sx);
       assertFalse(pair? sx);

       sx := convert "hello";
       assertFalse(null? sx);
       assertFalse(integer? sx);
       assertTrue(string? sx);
       assertFalse(symbol? sx);
       assertFalse(float? sx);
       assertFalse(pair? sx);

       sx := convert 12;
       assertFalse(null? sx);
       assertTrue(integer? sx);
       assertFalse(string? sx);
       assertFalse(symbol? sx);
       assertFalse(float? sx);
       assertFalse(pair? sx);

       sx := convert #"a";
       assertFalse(null? sx);
       assertFalse(integer? sx);
       assertFalse(string? sx);
       assertTrue(symbol? sx);
       assertFalse(float? sx);
       assertFalse(pair? sx);

       sx := convert 1.2;
       assertFalse(null? sx);
       assertFalse(integer? sx);
       assertFalse(string? sx);
       assertFalse(symbol? sx);
       assertTrue(float? sx);
       assertFalse(pair? sx);

       sx := cons(nil, nil);
       assertFalse(null? sx);
       assertFalse(integer? sx);
       assertFalse(string? sx);
       assertFalse(symbol? sx);
       assertFalse(float? sx);
       assertTrue(pair? sx);

       assertEquals("_"hello_"", unparse convert "hello");
       assertEquals("()", unparse nil);

       assertEquals("(1)", unparse cons(convert 1, nil));
       assertEquals("(1 . 2)", unparse cons(convert 1, convert 2));

       assertEquals("(1 2 3)", unparse cons(convert 1, 
       		       	 cons(convert 2, cons(convert 3, nil))));
       import from Assert Integer;

       sx := convert #"a";
       assertEquals("a", unparse sx);
       assertEquals("(a)", unparse(cons(sx, nil)));

       assertEquals(1, integer car(cons(convert 1, convert 2)));
       assertEquals(2, integer cdr(cons(convert 1, convert 2)));

       assertEquals(convert 1, convert 1);
       assertNotEquals(convert 1, convert 2);

       assertFalse(convert 1 = nil);


}

assertTrue(b: Boolean): () == if not b then never;
assertFalse(b: Boolean): () == if b then never;

assertEquals(s1: String, s2: String): () == {
       if not(s1 = s2) then 
            print concat("Not equal: ", concat(s1, concat(",", s2)));
}

assertEquals(s1: SExpression, s2: SExpression): () == {
       if not(s1 = s2) then 
            print concat("Not equal: ", concat(unparse s1, concat(",", unparse s2)));
}

assertNotEquals(s1: SExpression, s2: SExpression): () == {
       if (s1 = s2) then 
            print concat("Not equal: ", concat(unparse s1, concat(",", unparse s2)));
}

}


