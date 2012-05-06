--DEPS: Fraction_QuotientFieldCategory0 QuotientFieldCategory1 
--DEPS: CommonDenominator Matrix_MatrixCategory Vector
--DEPS: SparseUnivariatePolynomial_UnivariatePolynomialCategory

#include "axiom.as"
#pile

import from String;
import from System;

local xyzzy: with == add;

P ==> SparseUnivariatePolynomial %

extend Fraction(S: IntegralDomain): QuotientFieldCategory1 S with 
== add 
   import from OrderedSemiRingSegment NonNegativeInteger
   import from NonNegativeInteger
   import from Matrix S
   import from Integer
   import from Partial S
   import from S

   Rep ==> Record(num: S, den: S)
   import from Rep

 
   fUnion ==> ('nil,sqfr,irred,prime')
   QFP ==> SparseUnivariatePolynomial %
   F(X)  ==> Record(flg: fUnion, fctr: X, xpnt: Integer)
   import from F(P)
   import from UniversalSegment Integer
   import from CommonDenominator(S, %, Vector %)
   import from Record(fUnion, fctr:QFP, xpnt:Integer)

   local apply(a: %, p: 'num'): S == rep(a).num
   local apply(a: %, p: 'den'): S == rep(a).den

   reducedSystem(m:Matrix %, v:Vector %):
      Record(mat:Matrix S, vec:Vector S) ==
        n := reducedSystem(horizConcat(v::Matrix(%), m))@Matrix(S)
        [subMatrix(n, minRowIndex n, maxRowIndex n, 1 + minColIndex n,
                                maxColIndex n), column(n, minColIndex n)]

   reducedSystem(m:Matrix %):Matrix S ==
      import from Vector S
      nrm := nrows m
      ncm := ncols m
      ans : Matrix S := new(nrm, ncm, 0)$(Matrix S)
      for i in 1..nrm repeat
        d := commonDenominator(row(m, i::Integer))
        for j in 1..ncm repeat
          ell := qelt(m,i::Integer,j::Integer)
	  v: S := ((d exquo denom(ell))::S)*numer(ell)
          qsetelt!(ans, i::Integer, j::Integer, v)
      ans

   squareFreePolynomial(p: P): Factored P == never
   solveLinearPolynomialEquation(l: List P, p: P): Partial List P == never

   if S has PolynomialFactorizationExplicit0 then
       DP ==> SparseUnivariatePolynomial S
       import from UnivariatePolynomialCategoryFunctions2(%,QFP,S,DP)
       import from UnivariatePolynomialCategoryFunctions2(S,DP,%,QFP)
       -- we'll let the solveLinearPolynomialEquations operator
       -- default from Field
       default pp,qq: QFP
       default lpp: List QFP
       import from Factored SparseUnivariatePolynomial %

       if S has CharacteristicNonZero then
          if S has canonicalUnitNormal and S has GcdDomain then
             charthRoot(x: %): Partial % ==
               n := charthRoot x.num
               n case failed => [failed]
               d:=charthRoot x.den
               d case failed => [failed]
               [coerce(n)/coerce(d)]
          else
             charthRoot(x: %): Partial % ==
               -- to find x = p-th root of n/d
               -- observe that xd is p-th root of n*d^(p-1)
               ans:=charthRoot(x.num *
                      (x.den)^(characteristic()$%-1)::NonNegativeInteger)
               ans case failed => [failed]
               [coerce(ans)/ x.den]

          local clear(l: List %): List S ==
	     import from Fold S
             d:= lcm/[x.den for x in l]
             [ x.num * (d exquo x.den)::S for x in l]

          conditionP(mat: Matrix %): Partial Vector % ==
	    import from List List %
	    import from List List S
	    import from Partial Vector S
            local matD: Matrix S
            matD:= matrix [ clear l for l in listOfLists mat ]
            ansD := conditionP matD
            ansD case failed => [failed]
            ansDD:= ansD :: Vector(S)
            [[ ansDD(i::Integer)::% for i in 1..#ansDD]$Vector(%)]

       factorPolynomial(pp): Factored P ==
          SUPS ==> SparseUnivariatePolynomial S
	  import from Factored SUPS
	  import from List F(SUPS)
	  import from Fold S
	  import from List %
	  import from List S
          zero? pp => 0
          denpp:= lcm/[denom u for u in coefficients pp]
          ppD : DP := map((x: %): S +-> retract(x*denpp), pp)
          ff:=factorPolynomial ppD
          den1:%:=denpp::%
          local lfact:List Record(fUnion, fctr:QFP, xpnt:Integer)
          lfact:= ([[w.flg,
                    if leadingCoefficient w.fctr = 1 then
                        map((x: S): % +-> x::%, w.fctr)
                    else (lc:=(leadingCoefficient w.fctr)::%;
                           den1:=den1/lc^w.xpnt;
                            map((x: S): % +-> x::%/lc, w.fctr)),
                   w.xpnt] for w in factorList ff])
          makeFR(map((x: S): % +-> x::%/den1, unit(ff)), lfact)

       factorSquareFreePolynomial(pp): Factored P ==
          import from Fold S
          SUPS ==> SparseUnivariatePolynomial S
	  import from Factored SUPS
	  import from List F(SUPS)
	  import from List %
	  import from List S
          zero? pp => 0
          degree pp = 0 => makeFR(pp,empty())
          lcpp:=leadingCoefficient pp
          pp:=pp/lcpp
          denpp:= lcm/[denom u for u in coefficients pp]
          ppD : DP := map((x: %): S +-> retract(x*denpp), pp)
          ff:=factorSquareFreePolynomial ppD
          den1:%:=denpp::%/lcpp
          local lfact:List Record(fUnion, fctr:QFP, xpnt:Integer)
          lfact:= ([[w.flg,
                    if leadingCoefficient w.fctr = 1 then
                        map((x: S): % +-> x::%, w.fctr)
                    else (lc:=(leadingCoefficient w.fctr)::%;
                           den1:=den1/lc^w.xpnt;
                            map((x: S): % +-> x::%/lc, w.fctr)),
                   w.xpnt] for w in factorList ff])
          makeFR(map((x: S): % +-> x::%/den1, unit(ff)), lfact)
