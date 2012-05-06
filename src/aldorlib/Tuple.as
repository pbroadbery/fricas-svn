--DEPS: init_Generator PrimitiveArray
#include "axiom.as"

import from Boolean;

extend Tuple(T: Type): with {
   generator: % -> Generator T
}
== add {
   Rep == Record(n: Integer, arr: PrimitiveArray T);
   import from Rep;
   import from PrimitiveArray T;

   generator(t: %): Generator T == v for v in rep(t).arr;
}
