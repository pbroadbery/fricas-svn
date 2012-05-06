--DEPS: SetCategory init_List init_Boolean Integer_SetCategory String_SetCategory 
--DEPS: Symbol_SetCategory DoubleFloat_SetCategory 
--DEPS: runtime/ARCH/SExpression sexpr/SExpressionCategory

#include "axiom.as"

#pile
import from String

extend SExpression: SExpressionCategory(String, Symbol, Integer, DoubleFloat, OutputForm) with
== add 
   expr(a: %): OutputForm == a pretend OutputForm;
   convert(a: OutputForm): % == a pretend %;

   import from List OutputForm;
   import from List %;
   import from Integer
   import from NonNegativeInteger
   import from Symbol;

   dotex: OutputForm := convert(".") pretend OutputForm;
   coerce(b: %): OutputForm == 
            null? b => paren(empty()$OutputForm)
            atom? b => b pretend OutputForm
            r := b
            while not atom? r repeat r := cdr r
            l1 := [b1::OutputForm for b1 in (l := destruct b)]
            not null? r =>
              paren blankSeparate concat!(l1, [dotex, r::OutputForm])
            #l = 2::NonNegativeInteger 
	       and (convert first(l1) = convert(#"QUOTE"))@Boolean => quote first rest l1
            paren blankSeparate l1

