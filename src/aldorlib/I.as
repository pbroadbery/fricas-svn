--DEPS: lang Boolean
#include "axiom.as"

import from Boolean;

XAbelianMonoid: Category == with {
   1: %
}

XIndexedDirectProductCategory(R: with): Category == with {
  1: %;
}

XIndexedDirectProductObject(S: with): with XIndexedDirectProductCategory(S) == add {
    if S has XAbelianMonoid then 1: % == 1$S pretend %
}

A: XAbelianMonoid with == add { 1: % == never }
B: with { foo: () -> %; 1: % } == XIndexedDirectProductObject(A) add { foo(): % == 1 }

FM(T: XAbelianMonoid): with { XAbelianMonoid } == XIndexedDirectProductObject(T) add {
  foo(): % == never;
}


Foo: with {
   x: () -> %
} == add { x(): % == false pretend % }

Bar: with {
  y: () -> %;
  x: () -> %;
}
== Foo add {
  y(): % == x();
}