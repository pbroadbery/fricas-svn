--DEPS: lang Boolean

#include "axiom.as"

Assertions: with {
    assertTrue: Boolean -> ();
    assertFalse: Boolean -> ();
}
== add {
   assertTrue(v: Boolean): () == if not v then never;
   assertFalse(v: Boolean): () == if v then never;
}
