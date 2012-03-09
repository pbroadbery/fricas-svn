--DEPS: lang init_Generator Tuple
#include "axiom.as"

Stream(T: Type): with {
   generator: % -> Generator T;
   bracket: Tuple T -> %;
   stream: (() -> Generator T) -> %;
   append: (T, %) -> %;
   append: (%, %) -> %;
}
== add {
   Rep ==> () -> Generator T;
   generator(s: %): Generator T == rep(s)();
   
   bracket(t: Tuple T): % == stream((): Generator T +-> generator t);
   stream(g: ()-> Generator T): % == per g;
   append(a: %, b: %): % == stream( (): Generator T +-> generate { for x in a repeat yield x; for x in b repeat yield x});
   append(t: T, b: %): % == append([t], b);
}
