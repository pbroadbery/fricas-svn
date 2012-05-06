--DEPS:  OutputForm String
#include "axiom.as"

import from String;

Void: with {
   void: () -> %;            ++ void() produces a void object.
   coerce: % -> OutputForm;  ++ coerce(v) coerces void object to outputForm.
}
== add {
   Rep ==> String;
   void(): % == per "void";
   coerce(v:%): OutputForm == outputForm(rep(v));
}
