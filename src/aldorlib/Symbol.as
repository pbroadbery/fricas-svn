--DEPS: init_Symbol String

#include "axiom.as"

extend Symbol: with {
   coerce: String -> %;
   #: String -> %;
   =: (%, %) -> Boolean;
   name: % -> String;
   new: () -> %;
}
== add {
   Rep ==> String;
   import from String;
   coerce(x: String): % == per x;
   #(x: String): % == per x;
   name(a: %): String == rep a;

   (a: %) = (b: %): Boolean == rep a = rep b;

   new(): % == never;
}
