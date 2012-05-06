--DEPS: Boolean SetCategory Symbol OutputForm

#include "axiom.as"
#pile

extend Boolean: SetCategory with 
== add
   import from Symbol
   import from String
   coerce(b: %): OutputForm == outputForm(if b then #"true" else #"false")
