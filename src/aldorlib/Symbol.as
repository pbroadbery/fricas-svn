--DEPS: init_Symbol String

#include "axiom.as"

extend Symbol: with {
   coerce: String -> %;
   #: String -> %;
   =: (%, %) -> Boolean;
}
== add {
   Rep ==> String;
   import from String;
   coerce(x: String): % == per x;
   #(x: String): % == per x;
   
   (a: %) = (b: %): Boolean == rep a = rep b;
}
