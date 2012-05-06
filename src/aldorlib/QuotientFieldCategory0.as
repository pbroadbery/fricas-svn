--DEPS: IntegralDomain Field Algebra RetractableTo
#include "axiom.as"
#pile


QuotientFieldCategory0(S: IntegralDomain): Category ==
  Join(Field, Algebra S, RetractableTo S, FullyEvalableOver S,
         DifferentialExtension S) with
    /     : (S, S) -> %
       ++ d1 / d2 returns the fraction d1 divided by d2.
    numer  : % -> S
       ++ numer(x) returns the numerator of the fraction x.
    denom  : % -> S
       ++ denom(x) returns the denominator of the fraction x.
    numerator : % -> %
       ++ numerator(x) is the numerator of the fraction x converted to %.
    denominator : % -> %
       ++ denominator(x) is the denominator of the fraction x converted to %.

