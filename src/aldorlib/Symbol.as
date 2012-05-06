--DEPS: init_Symbol init_String

#include "axiom.as"

extend Symbol: with {
   coerce: String -> %;
   #: String -> %;
}
== add {
   -- Rep ==> Lisp Symbol
   coerce(x: String): % == never;
   #(x: String): % == never;
}
