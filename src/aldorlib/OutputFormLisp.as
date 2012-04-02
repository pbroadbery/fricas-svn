--DEPS: init_OutputForm init_List String Integer Symbol init_DoubleFloat init_NonNegativeInteger
--DEPS: NumberFormats Character_Base runtime/ARCH/SExpression
#include "axiom"

#pile
import from String;
import from IO;
OutputFormLisp: with 
     outformWidth: OutputForm -> Integer
     height: OutputForm -> Integer
     subspan: OutputForm -> Integer
     superspan: OutputForm -> Integer
     mathprint: SExpression -> ()
     fillerSpaces: (Integer, String) -> String;
  == add
     outformWidth(a: OutputForm): Integer == never;
     height(a: OutputForm): Integer == never;
     subspan(a: OutputForm): Integer == never;
     superspan(a: OutputForm): Integer == never;
     mathprint(a: SExpression): () == 
          import from Character
	  print("[");
          print(unparse(a) pretend LString);
	  print(concat("]", newline()) pretend LString)

     fillerSpaces(n: Integer, s: String): String == never;
