--DEPS: UniqueFactorizationDomain OrderedIntegralDomain DifferentialRing LinearlyExplicitRingOver
--DEPS: CharacteristicZero multiplicativeValuation EuclideanDomain PatternMatchable
--DEPS: CombinatorialFunctionCategory RealConstant StepThrough
#include "axiom"
#pile

IntegerNumberSystem0: Category ==
  Join(UniqueFactorizationDomain, EuclideanDomain, OrderedIntegralDomain,
         DifferentialRing, ConvertibleTo Integer, RetractableTo Integer,
           LinearlyExplicitRingOver Integer, ConvertibleTo InputForm,
             ConvertibleTo Pattern Integer, PatternMatchable Integer,
               CombinatorialFunctionCategory, RealConstant,
                 CharacteristicZero, StepThrough, canonicalUnitNormal,
                   multiplicativeValuation) with
   integer: Literal -> %		   
   odd?     : % -> Boolean
      ++ odd?(n) returns true if and only if n is odd.
   even?    : % -> Boolean
      ++ even?(n) returns true if and only if n is even.
   base     : () -> %
      ++ base() returns the base for the operations of \spad{IntegerNumberSystem}.
   length   : % -> %
      ++ length(a) length of \spad{a} in digits.
   shift    : (%, %) -> %
      ++ shift(a,i) shift \spad{a} by i digits.
   bit?     : (%, %) -> Boolean
      ++ bit?(n,i) returns true if and only if i-th bit of n is a 1.
   positiveRemainder     : (%, %) -> %
      ++ positiveRemainder(a,b) (where \spad{b > 1}) yields r
      ++ where \spad{0 <= r < b} and \spad{r == a rem b}.
   symmetricRemainder     : (%, %) -> %
      ++ symmetricRemainder(a,b) (where \spad{b > 1}) yields r
      ++ where \spad{ -b/2 <= r < b/2 }.
   rational?: % -> Boolean
      ++ rational?(n) tests if n is a rational number
      ++ (see \spadtype{Fraction Integer}).
   rational : % -> Fraction Integer
      ++ rational(n) creates a rational number (see \spadtype{Fraction Integer})..
   rationalIfCan: % -> Partial(Fraction Integer)
      ++ rationalIfCan(n) creates a rational number, or returns "failed" if this is not possible.
-- FIXME: strange random distribution used (#227).
   random   : () -> %
      ++ random() creates a random element. This function is deprecated.
   random   : % -> %
      ++ random(a) creates a random element from 0 to \spad{n-1}.
   hash     : % -> %
      ++ hash(n) returns the hash code of n.
   copy     : % -> %
      ++ copy(n) gives a copy of n.
   inc      : % -> %
      ++ inc(x) returns \spad{x + 1}.
   dec      : % -> %
      ++ dec(x) returns \spad{x - 1}.
   mask     : % -> %
      ++ mask(n) returns \spad{2^n-1} (an n bit mask).
   addmod   : (%,%,%) -> %
      ++ addmod(a,b,p), \spad{0<=a,b<p>1}, means \spad{a+b mod p}.
   submod   : (%,%,%) -> %
      ++ submod(a,b,p), \spad{0<=a,b<p>1}, means \spad{a-b mod p}.
   mulmod   : (%,%,%) -> %
      ++ mulmod(a,b,p), \spad{0<=a,b<p>1}, means \spad{a*b mod p}.
   powmod   : (%,%,%) -> %
      ++ powmod(a,b,p), \spad{0<=a,b<p>1}, means \spad{a^b mod p}.
   invmod   : (%,%) -> %
      ++ invmod(a,b), \spad{0<=a<b>1}, \spad{(a,b)=1} means \spad{1/a mod b}.

