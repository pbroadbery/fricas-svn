--DEPS: List OutputForm runtime/c/SExpression Tuple DoubleFloat String_SetCategory 
--DEPS: runtime/c/rtexns Integer_SetCategory
#include "axiom.as"

import from OutputForm;
import from String;
import from Integer;
import from Symbol;
import from DoubleFloat;

foo(): () == {
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

       assertEqual("_"hello_"", unparse convert "hello");
       assertEqual("()", unparse nil);

       assertEqual("(1)", unparse cons(convert 1, nil));
       assertEqual("(1 . 2)", unparse cons(convert 1, convert 2));

       assertEqual("(1 2 3)", unparse cons(convert 1, 
       		       	 cons(convert 2, cons(convert 3, nil))));
       import from Assertions Integer;

       assertEqual(1, integer car(cons(convert 1, convert 2)));
       assertEqual(2, integer cdr(cons(convert 1, convert 2)));

       assertEqual(convert 1, convert 1);
       assertNotEqual(convert 1, convert 2);

       assertFalse(convert 1 = nil);

}

assertTrue(b: Boolean): () == if not b then never;
assertFalse(b: Boolean): () == if b then never;

assertEqual(s1: String, s2: String): () == {
       if not(s1 = s2) then 
            print concat("Not equal: ", concat(s1, concat(",", s2)));
}

assertEqual(s1: SExpression, s2: SExpression): () == {
       if not(s1 = s2) then 
            print concat("Not equal: ", concat(unparse s1, concat(",", unparse s2)));
}

assertNotEqual(s1: SExpression, s2: SExpression): () == {
       if (s1 = s2) then 
            print concat("Not equal: ", concat(unparse s1, concat(",", unparse s2)));
}

local Assertions(T: SetCategory): with { assertEqual: (T, T) -> () }
== add {
   import from OutputForm;
   import from List OutputForm;
   import from String;

   assertEqual(s1: T, s2: T): () == {
       if not(s1 = s2) then 
            print commaSeparate [coerce "Not equal", coerce s1, coerce s2];
}
}

foo();
