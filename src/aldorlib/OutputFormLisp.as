--DEPS: init_OutputForm init_List String Integer Symbol init_DoubleFloat init_NonNegativeInteger
--DEPS: NumberFormats Character_Base 
#include "axiom"

#pile

OutputFormLisp: with 
     outformWidth: OutputForm -> Integer
     height: OutputForm -> Integer
     subspan: OutputForm -> Integer
     superspan: OutputForm -> Integer
     mathprint: OutputForm -> ()
     fillerSpaces: (Integer, String) -> String;
  == add
     outformWidth(a: OutputForm): Integer == never;
     height(a: OutputForm): Integer == never;
     subspan(a: OutputForm): Integer == never;
     superspan(a: OutputForm): Integer == never;
     mathprint(a: OutputForm): () == never;
     fillerSpaces(n: Integer, s: String): String == never;
