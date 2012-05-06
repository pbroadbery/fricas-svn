--DEPS: VectorCategory
#include "axiom.as"

Foo(X: shallowlyMutable): with { foo: () -> () } == add { foo(): () == never;}

AAA(V: VectorCategory Integer): () == { import from Foo V; foo()}