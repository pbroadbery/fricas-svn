--DEPS: IntegerNumberSystem0 NonNegativeInteger_SemiRing Set Vector
--DEPS: OrderedSemiRingSegment
#include "axiom.as"

import from String;
import from System;
#pile
IntegerRoots(I:IntegerNumberSystem0): Exports == Implementation where
  NNI ==> NonNegativeInteger
  Exports ==> with
    perfectNthPower?: (I, NNI) -> Boolean
      ++ \spad{perfectNthPower?(n,r)} returns true if n is an \spad{r}th
      ++ power and false otherwise
    perfectNthRoot: (I,NNI) -> Partial(I)
      ++ \spad{perfectNthRoot(n,r)} returns the \spad{r}th root of n if n
      ++ is an \spad{r}th power and returns "failed" otherwise
    perfectNthRoot: I -> Record(base:I, exponent:NNI)
      ++ \spad{perfectNthRoot(n)} returns \spad{[x,r]}, where \spad{n = x\^r}
      ++ and r is the largest integer such that n is a perfect \spad{r}th power
    approxNthRoot: (I,NNI) -> I
      ++ \spad{approxRoot(n,r)} returns an approximation x
      ++ to \spad{n^(1/r)} such that \spad{-1 < x - n^(1/r) < 1}
    perfectSquare?: I -> Boolean
      ++ \spad{perfectSquare?(n)} returns true if n is a perfect square
      ++ and false otherwise
    perfectSqrt: I -> Partial(I)
      ++ \spad{perfectSqrt(n)} returns the square root of n if n is a
      ++ perfect square and returns "failed" otherwise
    approxSqrt: I -> I
      ++ \spad{approxSqrt(n)} returns an approximation x
      ++ to \spad{sqrt(n)} such that \spad{-1 < x - sqrt(n) < 1}.
      ++ Compute an approximation s to \spad{sqrt(n)} such that
      ++           \spad{-1 < s - sqrt(n) < 1}
      ++ A variable precision Newton iteration is used.
      ++ The running time is \spad{O( log(n)^2 )}.

  Implementation ==> add
    import from IntegerPrimesPackage(I)
    import from NonNegativeInteger
    import from Partial I
    import from OrderedSemiRingSegment NNI

    default a, b, n: I

    resMod144: List I := [0::I,1::I,4::I,9::I,16::I,25::I,36::I,49::I,_
                     52::I,64::I,73::I,81::I,97::I,100::I,112::I,121::I]
    two := 2::I

    local coerce(i: I): NNI == 
       import from Integer
       convert(i)@Integer::NNI

    perfectSquare? a: Boolean       == (perfectSqrt a) case I
    perfectNthPower?(b, nni: NonNegativeInteger): Boolean == perfectNthRoot(b, nni) case I

    perfectNthRoot n: Record(base:I, exponent:NNI) ==  -- complexity (log log n)^2 (log n)^2
      import from Integer
      local m:NNI := 0
--      one? n or zero? n or n = -1 => [n, 1]
      (n = 1) or zero? n or n = -1 => [n, 1]
      e:NNI := 1
      p:NNI := (2@Integer)::NNI
      while p::Integer::I <= length(n) + 1 repeat
         for free m in 0.. while (r := perfectNthRoot(n, p)) case I repeat
            n := r::I
         e := e * p ^ m
         p := convert(nextPrime(p::Integer::I))@Integer :: NNI
      [n, e]

    approxNthRoot(a, nn: NNI): I ==   -- complexity (log log n) (log n)^2
      zero? nn => error "invalid arguments"
--      one? nn => a
      (nn = 1) => a
      nn = 2::NNI => approxSqrt a
      negative? a =>
        odd? nn => - approxNthRoot(-a, nn)
        0
      zero? a => 0
--      one? a => 1
      (a = 1) => 1
      -- quick check for case of large n
      ((3*nn::Integer::I) quo 2) >= (l := length a) => two
      -- the initial approximation must be >= the root
      y := max(two, shift(1, (nn::Integer::I+l-1) quo (nn::Integer::I)))
      z:I := 1
      n1 := prev nn
      while z > 0 repeat
        x := y
        xn:= x^n1
        y := (n1*x*xn+a) quo (nn*xn)
        z := x-y
      x

    local prev(nn: NNI): NNI == 
      import from Integer
      (nn-1)::NNI

    perfectNthRoot(b: I, nn: NNI): Partial I ==
      (r := approxNthRoot(b, nn)) ^(nn) = b => [r]
      [failed]

    perfectSqrt a: Partial I ==
      a < 0 or not member?(a rem (144::I), resMod144) => [failed]
      (s := approxSqrt a) * s = a => [s]
      [failed]

    approxSqrt a: I ==
      a < 1 => 0
      if (n := length a) > (100::I) then
         -- variable precision newton iteration
         n := n quo (4::I)
         s := approxSqrt shift(a, -2 * n)
         s := shift(s, n)
         return ((1 + s + a quo s) quo two)
      -- initial approximation for the root is within a factor of 2
      (new: I, old: I) := (shift(1, n quo two), 1)
      while new ~= old repeat
         (new, old) := ((1 + new + a quo new) quo two, new)
      new

IntegerPrimesPackage(I: IntegerNumberSystem0): Exports == Implementation where
 NNI ==> NonNegativeInteger
 Exports ==> with
   prime?: I -> Boolean
     ++ \spad{prime?(n)} returns true if n is prime and false if not.
     ++ Note that we ignore sign of n, so -5 is considered prime.
     ++ The algorithm used is Rabin's probabilistic primality test
     ++ (reference: Knuth Volume 2 Semi Numerical Algorithms).
     ++ If \spad{prime? n} returns false, n is proven composite.
     ++ If \spad{prime? n} returns true, prime? may be in error
     ++ however, the probability of error is very low.
     ++ and is zero below 25*10^9 (due to a result of Pomerance et al),
     ++ below 10^12 and 10^13 due to results of Pinch,
     ++ and below 341550071728321 due to a result of Jaeschke.
     ++ Specifically, this implementation does at least 10 pseudo prime
     ++ tests and so the probability of error is \spad{< 4^(-10)}.
     ++ The running time of this method is cubic in the length
     ++ of the input n, that is \spad{O( (log n)^3 )}, for n<10^20.
     ++ beyond that, the algorithm is quartic, \spad{O( (log n)^4 )}.
     ++ Two improvements due to Davenport have been incorporated
     ++ which catches some trivial strong pseudo-primes, such as
     ++ [Jaeschke, 1991] 1377161253229053 * 413148375987157, which
     ++ the original algorithm regards as prime
   nextPrime: I -> I
     ++ \spad{nextPrime(n)} returns the smallest prime strictly larger than n
   prevPrime: I -> I
     ++ \spad{prevPrime(n)} returns the largest prime strictly smaller than n
   primes: (I,I) -> List I
     ++ \spad{primes(a,b)} returns a list of all primes p with
     ++ \spad{a <= p <= b}
 Implementation ==> add
   default m, n, a, b, i: I
   smallPrimes: List I := [2::I,3::I,5::I,7::I,11::I,13::I,17::I,19::I,_
                      23::I,29::I,31::I,37::I,41::I,43::I,47::I,_
                      53::I,59::I,61::I,67::I,71::I,73::I,79::I,_
                      83::I,89::I,97::I,101::I,103::I,107::I,109::I,_
                      113::I,127::I,131::I,137::I,139::I,149::I,151::I,_
                      157::I,163::I,167::I,173::I,179::I,181::I,191::I,_
                      193::I,197::I,199::I,211::I,223::I,227::I,229::I,_
                      233::I,239::I,241::I,251::I,257::I,263::I,269::I,_
                      271::I,277::I,281::I,283::I,293::I,307::I,311::I,_
                      313::I]
   import from Fold I
   import from UniversalSegment I

   productSmallPrimes    := (*)/smallPrimes
   nextSmallPrime        := 317::I
   nextSmallPrimeSquared := nextSmallPrime^(2::NNI)
   two                   := 2::I
   tenPowerTwenty:=(10::I)^(20::NNI)
   PomeranceList:= [25326001::I, 161304001::I, 960946321::I, 1157839381::I,
                     -- 3215031751::I, -- has a factor of 151
                     3697278427::I, 5764643587::I, 6770862367::I,
                      14386156093::I, 15579919981::I, 18459366157::I,
                       19887974881::I, 21276028621::I ]@(List I)
   PomeranceLimit:=27716349961::I  -- replaces (25*10^9) due to Pinch
   PinchList:= [3215031751::I, 118670087467::I, 128282461501::I, 354864744877::I,
                546348519181::I, 602248359169::I, 669094855201::I ]
   PinchLimit:= 10^(12::NNI)
   PinchList2:= [2152302898747::I, 3474749660383::I]
   PinchLimit2:= 10^(13::NNI)
   JaeschkeLimit:=341550071728321::I
   rootsMinus1:Set I := empty()
   -- used to check whether we detect too many roots of -1
   count2Order:Vector NonNegativeInteger := 
      import from NonNegativeInteger
      new(1, 0)
   -- used to check whether we observe an element of maximal two-order

   primes(m, n): List I ==
      -- computes primes from m to n inclusive using prime?
      l:List(I) :=
        m <= two => [two]
        empty()
      n < two or n < m => empty()
      if even? m then m := m + 1
      ll:List(I) := [k for k in m..n by convert(2)@Integer | prime?(k)$%]
--             convert(m)@Integer..convert(n)@Integer by convert(2)@Integer | prime?(k::I)]
      reverse! concat!(ll, l)

   rabinProvesComposite : (I,I,I,I,NonNegativeInteger) -> Boolean
   rabinProvesCompositeSmall : (I,I,I,I,NonNegativeInteger) -> Boolean


   rabinProvesCompositeSmall(p: I,n: I,nm1: I,q: I , k: NonNegativeInteger): Boolean ==
         -- probability n prime is > 3/4 for each iteration
         -- for most n this probability is much greater than 3/4
         t := powmod(p, q, n)
         -- neither of these cases tells us anything
--         if not (one? t or t = nm1) then
         if not ((t = 1) or t = nm1) then
            for j in 1..(k-1)::I repeat
               oldt := t
               t := mulmod(t, t, n)
--               one? t => return true
               (t = 1) => return true
               -- we have squared something not -1 and got 1
               t = nm1 => break
            not (t = nm1) => return true
         false

   rabinProvesComposite(p: I,n: I,nm1: I,q: I,k: NonNegativeInteger): Boolean ==
         -- probability n prime is > 3/4 for each iteration
         -- for most n this probability is much greater than 3/4
	 import from Integer
	 free rootsMinus1;
         t := powmod(p, q, n)
         -- neither of these cases tells us anything
         if t=nm1 then count2Order(1$Integer):=count2Order(1$Integer)+1
--         if not (one? t or t = nm1) then
         if not ((t = 1) or t = nm1) then
            for j in 1..(k-1)::I repeat
               oldt := t
               t := mulmod(t, t, n)
--               one? t => return true
               (t = 1) => return true
               -- we have squared something not -1 and got 1
               t = nm1 =>
                   rootsMinus1:=union(rootsMinus1,oldt)
                   count2Order((j+1)::Integer):=count2Order((j+1)::Integer)+1
                   break
            not (t = nm1) => return true
         # rootsMinus1 > 2@Integer::NNI => true  -- Z/nZ can't be a field
         false

   prime? n: Boolean ==
      import from OrderedSemiRingSegment NNI
      if n < -1 then n := -n
      n < two => false
      n < nextSmallPrime => member?(n, smallPrimes)
--      not one? gcd(n, productSmallPrimes) => false
      not (gcd(n, productSmallPrimes) = 1) => false
      n < nextSmallPrimeSquared => true

      nm1 := n-1
      q := (nm1) quo two
      k: NNI := 0
      for free k in 1.. while not odd? q repeat q := q quo two
      -- q = (n-1) quo 2^k for largest possible k

      n < JaeschkeLimit =>
          rabinProvesCompositeSmall(2,n,nm1,q,k) => return false
          rabinProvesCompositeSmall(3,n,nm1,q,k) => return false

          n < PomeranceLimit =>
              rabinProvesCompositeSmall(5,n,nm1,q,k) => return false
              member?(n,PomeranceList) => return false
              true

          rabinProvesCompositeSmall(7,n,nm1,q,k) => return false
          n < PinchLimit =>
              rabinProvesCompositeSmall(10,n,nm1,q,k) => return false
              member?(n,PinchList) => return false
              true

          rabinProvesCompositeSmall(5,n,nm1,q,k) => return false
          rabinProvesCompositeSmall(11,n,nm1,q,k) => return false
          n < PinchLimit2 =>
              member?(n,PinchList2) => return false
              true

          rabinProvesCompositeSmall(13,n,nm1,q,k) => return false
          rabinProvesCompositeSmall(17,n,nm1,q,k) => return false
          true

      rootsMinus1: List I := empty()
      count2Order: Vector I := new(k,0) -- vector of k zeroes

      import from UniversalSegment Integer
      import from Integer

      mn := minIndex smallPrimes
      for ii in mn+1..mn+10 repeat
          rabinProvesComposite(smallPrimes ii,n,nm1,q,k) => return false
      import from IntegerRoots(I)
      q > 1 and perfectSquare?(3@I*n+1) => false
      ((n9:=n rem (9))=1 or n9 = -1) and perfectSquare?(8@I*n+1) => false
      -- Both previous tests from Damgard & Landrock
      currPrime:=smallPrimes(mn+10)
      probablySafe:=tenPowerTwenty
      while count2Order(k::Integer) = 0 or n > probablySafe repeat
          currPrime := nextPrime currPrime
          probablySafe:=probablySafe*(100@I)
          rabinProvesComposite(currPrime,n,nm1,q,k) => return false
      true

   nextPrime(n: I): I ==
      -- computes the first prime after n
      n < two => two
      if odd? n then n := n + two else n := n + 1
      while not(prime?(n)$%) repeat n := n + two
      n

   prevPrime n: I ==
      -- computes the first prime before n
      n < 3::I => error "no primes less than 2"
      n = 3::I => two
      if odd? n then n := n - two else n := n - 1
      while not(prime?(n)$%) repeat n := n - two
      n

   local coerce(i: I): NNI == 
       import from Integer
       convert(i)@Integer::NNI

   local coerce(i: I): Integer == 
       import from Integer
       convert(i)@Integer

