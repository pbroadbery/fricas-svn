--DEPS: lang Generator
#include "axiom.as"

Stream(T: Type): with {
   generator: % -> Generator T;
   bracket: Tuple T -> T;
   stream: (() -> Generator T) -> %;
   append: (T, %) -> %;
   append: (%, %) -> %;
}
== add {
   Rep ==> () -> Generator T;
   generator(s: %): Generator T == rep(s)();
   bracket(t: Tuple T): % == stream((): Generator T +-> generator t);
   bracket(g: ()-> Generator T): % == per g;
   append(a: %, b: %): % == stream( (): Generator T +-> generate { yield x for x in a; yield x for x in b}
   append(t: T, b: %): % == append([t], b);
}
