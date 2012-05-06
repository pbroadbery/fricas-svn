--DEPS:  Integer_IntegralDomain RealConstant InputForm PatternMatchable init_Pattern
#include "axiom.as"

import from Boolean;
#pile
extend Integer: Join(RealConstant, ConvertibleTo InputForm, 
       		     ConvertibleTo Pattern %, PatternMatchable %) with
   coerce: % -> DoubleFloat 
   coerce: % -> Float
   coerce: % -> Pattern %
== add 
   convert(n: %): DoubleFloat == never
   convert(n: %): Float == never
   coerce(n: %): DoubleFloat == never
   coerce(n: %): Float == never

   convert(n: %): InputForm == never
   
   convert(x: %): Pattern(%) == never
   coerce(x: %): Pattern(%) == never
   patternMatch(n: %, p: Pattern(%), qq: PatternMatchResult(%, %)): PatternMatchResult(%, %) == never
