--DEPS: Fraction_DivisionRing QuotientFieldCategory0 

#include "axiom.as"
#pile

import from String;
import from System;

extend Fraction(S: IntegralDomain): QuotientFieldCategory0 S with 
== add 
   import from S
   import from Integer
   import from Partial S
   import from NonNegativeInteger

   Rep ==> Record(num: S, den: S)
   import from Rep
   local apply(a: %, p: 'num'): S == rep(a).num
   local apply(a: %, p: 'den'): S == rep(a).den

   divide(a: %, b: %): Record(quotient: %, remainder: %) == never;
   (s: S) * (a: %): % == s::% * a;
   (a: %) * (s: S): % == a * s::%;

   numerator(a:%): % == coerce a.num
   denominator(a:%): % == coerce a.den

   if S has GcdDomain and S has canonicalUnitNormal then
      retract(x:%):S ==
--        one?(x.den) => x.num
        ((x.den) = 1) => x.num
        error "Denominator not equal to 1"

      retractIfCan(x:%): Partial S ==
--        one?(x.den) => [x.num]
        ((x.den) = 1) => [x.num]
        [failed]
   else
      retract(x:%):S ==
        (a:= x.num exquo x.den) case failed =>
           error "Denominator not equal to 1"
        a::S
      retractIfCan(x:%): Partial S == x.num exquo x.den

   map(fn: S -> S, x: %): % == (fn numer x) / (fn denom x)

   differentiate(x:%, deriv:S -> S): % ==
        import from Integer
        n := numer x
        d := denom x
        (deriv n * d - n * deriv d) / (d^(2::NonNegativeInteger))

