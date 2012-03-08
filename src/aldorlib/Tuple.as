--DEPS: init_Generator init_Boolean SingleInteger
#include "axiom.as"

import from Boolean;

extend Tuple(T: Type): with {
   #: % -> SingleInteger;
   apply: (%, SingleInteger) -> T;
   generator: % -> Generator T;
} 
== add {
   import from Machine;
   Rep ==> Record(n: SingleInteger, p: Arr);
   import from Rep;
   #(x: %): SingleInteger == rep(x).n;

   apply(t: %, n: SingleInteger): T == { CHK(t, n); get(T)(rep(t).p, n pretend SInt);}
   local CHK(t: %, n: SingleInteger): () == if n >= #t then never;

   generator(x: %): Generator T == generate {
      n: SInt := 0;
      len := #x pretend SInt;
      while (n < len) pretend Boolean repeat { yield x.(n pretend SingleInteger); n := n + 1}
   }
}
