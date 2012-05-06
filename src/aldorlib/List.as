#include "axiom.as"

import from Boolean;

extend List(T: Type): BasicType with {
  nil: () -> %;
  null?: % -> Boolean;
  cons: (T, %) -> %;
  bracket: Tuple T -> %;
  bracket: Generator T -> %;
  generator: % -> Generator T;
  #: % -> NonNegativeInteger;

  if T has SetCategory then {
     reduce: ((T, T) -> T, %, T, T) -> T;
  }
}
 == add {
  Rep ==> XLisp;
  import from Rep;
  nil(): % == per NIL();
  null?(x: %): Boolean == NULL?(rep(x));
  (a: %) = (b: %): Boolean == never;
  [t: Tuple T]: % == never;
  [t: Generator T]: % == never;
  cons(e: T, l: %): % == per CONS(lisp(T)(e), rep l);
  generator(l: %): Generator T == never;
  #(x: %): NonNegativeInteger == never;

  if T has SetCategory then {
    reduce(f: (T, T) -> T, l: %, init: T, absorb: T): T == {
     acc := init;
     for item in l repeat {
        item = absorb => return absorb;
	acc := f(acc, item);
     }
     acc
  }
}
}

