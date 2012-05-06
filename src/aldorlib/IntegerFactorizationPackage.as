--DEPS: IntegerNumberSystem0
#include "axiom.as"
#pile

IntegerFactorizationPackage(I: IntegerNumberSystem0): Exports == Implementation where
    FF      ==> Factored I
    Exports ==> with			       
	factor: I -> Factored I
	squareFree: I -> FF
    Implementation ==> add
   	factor(i: I): Factored I == never;
	squareFree(i: I): Factored I == never
#if 0
IntegerFactorizationPackage(I): Exports == Implementation where
  I: IntegerNumberSystem

  B      ==> Boolean
  FF     ==> Factored I
  NNI    ==> NonNegativeInteger
  LMI    ==> ListMultiDictionary I
  FFE    ==> Record(flg:Union("nil","sqfr","irred","prime"),
                                                   fctr:I, xpnt:Integer)

  Exports ==>  with
    factor : I -> FF
      ++ factor(n) returns the full factorization of integer n
    squareFree   : I -> FF
      ++ squareFree(n) returns the square free factorization of integer n
    BasicMethod : I -> FF
      ++ BasicMethod(n) returns the factorization
      ++ of integer n by trial division
    PollardSmallFactor: I -> Union(I,"failed")
       ++ PollardSmallFactor(n) returns a factor
       ++ of n or "failed" if no one is found

  Implementation ==> add
    import IntegerRoots(I)

    BasicSieve: (I, I) -> FF

    squareFree(n:I):FF ==
       u:I
       if n<0 then (m := -n; u := -1)
              else (m := n; u := 1)
       (m > 1) and ((v := perfectSqrt m) case I) =>
          for rec in (l := factorList(sv := squareFree(v::I))) repeat
            rec.xpnt := 2 * rec.xpnt
          makeFR(u * unit sv, l)
    -- avoid using basic sieve when the lim is too big
       lim := 1 + approxNthRoot(m,3)
       lim > (100000::I) => makeFR(u, factorList factor m)
       x := BasicSieve(m, lim)
       y :=
--         one?(m:= unit x) => factorList x
         ((m:= unit x) = 1) => factorList x
         (v := perfectSqrt m) case I =>
            concat!(factorList x, ["sqfr",v,2]$FFE)
         concat!(factorList x, ["sqfr",m,1]$FFE)
       makeFR(u, y)

    -- Pfun(y: I,n: I): I == (y^2 + 5) rem n
    PollardSmallFactor(n:I):Union(I,"failed") ==
       -- Use the Brent variation
-- FIXME: strange random distribution used (#227).
       x0 := random()$I
       m := 100::I
       y := x0 rem n
       r:I := 1
       q:I := 1
       G:I := 1
       l:I
       k:I
       until G > 1 repeat
          x := y
          ys := y
          for i in 1..convert(r)@Integer repeat
             y := (y*y+5::I) rem n
             q := (q*abs(x-y)) rem n
          k := 0::I
          G := gcd(q,n)
          until (k>=r) or (G>1) repeat
             ys := y
             for i in 1..convert(min(m,r-k))@Integer repeat
                y := (y*y+5::I) rem n
                q := (q*abs(x-y)) rem n
             G := gcd(q,n)
             k := k+m
          k := k + r
          r := 2*r
       if G=n then
          l := k - m
          G := 1::I
          until G>1 repeat
             ys := (ys*ys+5::I) rem n
             G := gcd(abs(x-ys),n)
             l := l + 1
          if G = n then
             y := x0
             x := x0
             for i in 1..convert(l)@Integer repeat
               y := (y*y+5::I) rem n
             G := gcd(abs(x-y), n)
             until G>1 repeat
               y := (y*y+5::I) rem n
               x := (x*x+5::I) rem n
               G := gcd(abs(x-y), n)
       G=n => "failed"
       G

    PollardSmallFactor20(n:I):Union(I,"failed") ==
       for i in 1..20 repeat
          r := PollardSmallFactor n
          r case I => return r
       r

    BasicSieve(r, lim) ==
       l:List(I) :=
          [1::I,2::I,2::I,4::I,2::I,4::I,2::I,4::I,6::I,2::I,6::I]
       concat!(l, rest(l, 3))
       d := 2::I
       n := r
       ls := empty()$List(FFE)
       for s in l repeat
          d > lim => return makeFR(n, ls)
          if n<d*d then
             if n>1 then ls := concat!(ls, ["prime",n,1]$FFE)
             return makeFR(1, ls)
          for m in 0.. while zero?(n rem d) repeat n := n quo d
          if m>0 then ls := concat!(ls, ["prime",d,convert m]$FFE)
          d := d+s

    BasicMethod n ==
       u:I
       if n<0 then (m := -n; u := -1)
              else (m := n; u := 1)
       x := BasicSieve(m, 1 + approxSqrt m)
       makeFR(u, factorList x)

    factor m ==
       u:I
       zero? m => 0
       if negative? m then (n := -m; u := -1)
                      else (n := m; u := 1)
       b := BasicSieve(n, 10000::I)
       flb := factorList b
--       one?(n := unit b) => makeFR(u, flb)
       ((n := unit b) = 1) => makeFR(u, flb)
       a:LMI := dictionary() -- numbers yet to be factored
       b:LMI := dictionary() -- prime factors found
       f:LMI := dictionary() -- number which could not be factored
       insert!(n, a)
       while not empty? a repeat
          n := inspect a; c := count(n, a); remove!(n, a)
          prime?(n)$IntegerPrimesPackage(I) => insert!(n, b, c)
          -- test for a perfect power
          (s := perfectNthRoot n).exponent > 1 =>
            insert!(s.base, a, c * s.exponent)
          -- test for a difference of square
          x := approxSqrt n
          if (x^2<n) then x:=x+1
          (y:=perfectSqrt (x^2-n)) case I =>
                insert!(x+y,a,c)
                insert!(x-y,a,c)
          (d := PollardSmallFactor20 n) case I =>
             for m in 0.. while zero?(n rem d) repeat n := n quo d
             insert!(d, a, m * c)
             if n > 1 then insert!(n, a, c)
          -- an elliptic curve factorization attempt should be made here
          insert!(n, f, c)
       -- insert prime factors found
       while not empty? b repeat
          n := inspect b; c := count(n, b); remove!(n, b)
          flb := concat!(flb, ["prime",n,convert c]$FFE)
       -- insert non-prime factors found
       while not empty? f repeat
          n := inspect f; c := count(n, f); remove!(n, f)
          flb := concat!(flb, ["nil",n,convert c]$FFE)
       makeFR(u, flb)
#endif