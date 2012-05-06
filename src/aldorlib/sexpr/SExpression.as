--DEPS: sexpr/init_SExpression sexpr/SExpressionOf 
--DEPS: String_SetCategory Symbol_SetCategory Integer_SetCategory DoubleFloat_SetCategory
#include "axiom.as"

SExpression: SExpressionCategory(String, Symbol, Integer, DoubleFloat, OutputForm)
  == SExpressionOf(String, Symbol, Integer, DoubleFloat, OutputForm)
