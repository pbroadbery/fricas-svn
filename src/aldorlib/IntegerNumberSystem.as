--DEPS: IntegerNumberSystem0 Integer_RealConstant IntegerFactorizationPackage
--DEPS: IntegerPrimesPackage
#include "axiom"
#pile

import from String
import from System

IntegerNumberSystem: Category == IntegerNumberSystem0 with
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

   default
    default a, b, n, m, x, i: %
    import from Integer

    characteristic(): NonNegativeInteger == 0
    differentiate x: %          == 0
    even? x: Boolean            == not odd? x
    positive? x: Boolean        == x > 0
    copy x: %                   == x
    bit?(x, i): Boolean         == odd? shift(x, -i)
    mask n: %                   == dec shift(1, n)
    rational? x: Boolean        == true
    euclideanSize(x): NonNegativeInteger ==
        x=0 => error "euclideanSize called on zero"
        x<0 => (-convert(x)@Integer)::NonNegativeInteger
        convert(x)@Integer::NonNegativeInteger
    convert(x:%):Float       == (convert(x)@Integer)::Float
    convert(x:%):DoubleFloat  == (convert(x)@Integer)::DoubleFloat
    convert(x:%):InputForm   == convert(convert(x)@Integer)$Integer
    retract(x:%):Integer     == convert(x)@Integer
    convert(x:%):Pattern(Integer)== convert(x)@Integer ::Pattern(Integer)
    factor x: Factored %         == factor(x)$IntegerFactorizationPackage(%)
    squareFree x: Factored % == squareFree(x)$IntegerFactorizationPackage(%)
    prime? x: Boolean    == prime?(x)$IntegerPrimesPackage(%)
    factorial x: %       == factorial(x)$IntegerCombinatoricFunctions(%)
    binomial(n, m): %    == binomial(n, m)$IntegerCombinatoricFunctions(%)
    permutation(n, m): % == permutation(n,m)$IntegerCombinatoricFunctions(%)
    retractIfCan(x:%): Partial(Integer) == convert(x)@Integer

    init(): % == 0

   -- iterates in order 0,1,-1,2,-2,3,-3,...
    nextItem(n): % ==
     zero? n => 1
     n>0 => -n
     1-n

    patternMatch(x, p: Pattern Integer, l: PatternMatchResult(Integer, %)): PatternMatchResult(Integer, %) ==
     patternMatch(x, p, l)$PatternMatchIntegerNumberSystem(%)

    rational(x:%):Fraction(Integer) ==
     (convert(x)@Integer)::Fraction(Integer)

    rationalIfCan(x:%): Partial(Fraction Integer) ==
     (convert(x)@Integer)::Fraction(Integer)

    symmetricRemainder(x, n): % ==
      r := x rem n
      r = 0 => r
      if n < 0 then n:=-n
      r > 0 =>
         2 * r > n => r - n
         r
      2*r + n <= 0 => r + n
      r

    invmod(a, b): % ==
      if negative? a then a := positiveRemainder(a, b)
      c := a; c1:% := 1
      d := b; d1:% := 0
      while not zero? d repeat
         q := c quo d
         r := c-q*d
         r1 := c1-q*d1
         c := d; c1 := d1
         d := r; d1 := r1
--      not one? c => error "inverse does not exist"
      not (c = 1) => error "inverse does not exist"
      negative? c1 => c1 + b
      c1

    powmod(x, n, p: %): % ==
      if negative? x then x := positiveRemainder(x, p)
      zero? x => 0
      zero? n => 1
      y:% := 1
      z := x
      repeat
         if odd? n then y := mulmod(y, z, p)
         zero?(n := shift(n, -1)) => return y
         z := mulmod(z, z, p)
