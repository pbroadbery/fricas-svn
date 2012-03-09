--DEPS: String runtime/c/rtexns SingleInteger
#include "axiom.as"

import from String;
import from SingleInteger;
import from Integer;
      
foo(): () == {	
       # "hello" ~= 5::SingleInteger => never;
       if not empty? "" then never;
       s := concat("H", "W");
       if # s ~= 2::SingleInteger then never;
       if not("hello" = "hello") then never;
       if "" = "x" then never;
       if not("abc" = "abc") then never;
       if not("helloworld" = concat("hello", "world")) then never;
       "done"
}


foo();

