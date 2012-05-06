--DEPS:  lang Boolean List
#include "axiom"

import from Boolean;

SetC: Category == with;

L(T: with): with {
   empty: () -> %;
   if T has SetC then { removeDuplicates: % -> %; }
} == add {
   empty(): % == never;
   if T has SetC then { removeDuplicates(x: %): % == x}
}


Foo(S: with): Category == with {
       
       if S has SetCategory then { SetCategory ; fn: () -> () };
       default {
       	       if S has SetCategory then {
       	       fn(): () == {
	       	     import from List %;
		     l := empty();
		     removeDuplicates(l)
	       }}
       }
}
