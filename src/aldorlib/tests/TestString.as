--DEPS: String runtime/ARCH/rtexns SingleInteger tests/Assert tests/TestCategory
#include "axiom.as"

import from String;
import from SingleInteger;
import from Integer;
import from Assert String;
import from Character;

TestString: TestCategory with {
}
== add {
test(): () == {	
       
       # "hello" ~= 5::SingleInteger => never;
       if not empty? "" then never;
       s := concat("H", "W");
       if # s ~= 2::SingleInteger then never;
       if not("hello" = "hello") then never;
       if "" = "x" then never;
       if not("abc" = "abc") then never;
       if not("helloworld" = concat("hello", "world")) then never;
       
       assertEquals("", new(0::NonNegativeInteger, char "a"));
       assertEquals("a", new(1::NonNegativeInteger, char "a"));
       assertEquals("aaa", new(3::NonNegativeInteger, char "a"));

       assertEquals("a123", concat(char "a", "123"));
       assertEquals("123a", concat("123", char "a"));

       "done"
}


}

