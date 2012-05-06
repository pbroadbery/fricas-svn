--DEPS: Ring PolynomialCategory0 SingletonAsOrderedSet NonNegativeInteger_OrderedAbelianMonoidSup
--DEPS: Eltable DifferentialRing DifferentialExtension Vector_FiniteLinearAggregate 
#include "axiom"

import from Boolean;
import from System;
import from String;
-- UPC, limited to the unconditional exports
#pile
+++ Author:
+++ Date Created:
+++ Date Last Updated:
+++ Basic Functions: Ring, monomial, coefficient, reductum, differentiate,
+++ elt, map, resultant, discriminant
+++ Related Constructors:
+++ Also See:
+++ AMS Classifications:
+++ Keywords:
+++ References:
+++ Description:
+++ The category of univariate polynomials over a ring R.
+++ No particular model is assumed - implementations can be either
+++ sparse or dense.

UnivariatePolynomialCategory0(R:Ring): Category ==
 Join(PolynomialCategory0(R, NonNegativeInteger, SingletonAsOrderedSet),
      Eltable(R, R), Eltable(%, %), DifferentialRing,
      DifferentialExtension R) with
   vectorise        : (%,NonNegativeInteger) -> Vector R
     ++ vectorise(p, n) returns \spad{[a0,...,a(n-1)]} where
     ++ \spad{p = a0 + a1*x + ... + a(n-1)*x^(n-1)} + higher order terms.
     ++ The degree of polynomial p can be different from \spad{n-1}.
   makeSUP: % -> SparseUnivariatePolynomial R
     ++ makeSUP(p) converts the polynomial p to be of type
     ++ SparseUnivariatePolynomial over the same coefficients.
   unmakeSUP: SparseUnivariatePolynomial R -> %
     ++ unmakeSUP(sup) converts sup of type \spadtype{SparseUnivariatePolynomial(R)}
     ++ to be a member of the given type.
     ++ Note: converse of makeSUP.
   multiplyExponents: (%,NonNegativeInteger) -> %
     ++ multiplyExponents(p,n) returns a new polynomial resulting from
     ++ multiplying all exponents of the polynomial p by the non negative
     ++ integer n.
   divideExponents: (%,NonNegativeInteger) -> Partial %
     ++ divideExponents(p,n) returns a new polynomial resulting from
     ++ dividing all exponents of the polynomial p by the non negative
     ++ integer n, or "failed" if some exponent is not exactly divisible
     ++ by n.
   monicDivide: (%,%) -> Record(quotient:%,remainder:%)
     ++ monicDivide(p,q) divide the polynomial p by the monic polynomial q,
     ++ returning the pair \spad{[quotient, remainder]}.
     ++ Error: if q isn't monic.
-- These three are for Karatsuba
   karatsubaDivide: (%,NonNegativeInteger) -> Record(quotient:%,remainder:%)
     ++ \spad{karatsubaDivide(p,n)} returns the same as \spad{monicDivide(p,monomial(1,n))}
   shiftRight: (%,NonNegativeInteger) -> %
     ++ \spad{shiftRight(p,n)} returns \spad{monicDivide(p,monomial(1,n)).quotient}
   shiftLeft: (%,NonNegativeInteger) -> %
     ++ \spad{shiftLeft(p,n)} returns \spad{p * monomial(1,n)}
   pseudoRemainder: (%,%) -> %
      ++ pseudoRemainder(p,q) = r, for polynomials p and q, returns the remainder when
      ++ \spad{p' := p*lc(q)^(deg p - deg q + 1)}
      ++ is pseudo right-divided by q, i.e. \spad{p' = s q + r}.
   differentiate: (%, R -> R, %) -> %
      ++ differentiate(p, d, x') extends the R-derivation d to an
      ++ extension D in \spad{R[x]} where Dx is given by x', and returns \spad{Dp}.
   default
    default pp,qq: SparseUnivariatePolynomial %
    default p, q, sp: %
    default n: NonNegativeInteger
    import from SingletonAsOrderedSet
    import from R
    import from Record(quotient:%,remainder:%)
    import from UniversalSegment Integer
    import from Integer

    variables(p): List SingletonAsOrderedSet ==
      zero? p or zero?(degree p) => []
      [create()]
    degree(p:%,v:SingletonAsOrderedSet): NonNegativeInteger == degree p

    totalDegree(p:%,lv:List SingletonAsOrderedSet): NonNegativeInteger ==
       empty? lv => 0
       totalDegree p

    degree(p:%,lv:List SingletonAsOrderedSet): List NonNegativeInteger ==
       empty? lv => []
       [degree p]

    eval(p:%,lv: List SingletonAsOrderedSet,lq: List %):% ==
      empty? lv => p
      not empty? rest lv => error "can only eval a univariate polynomial once"
      eval(p,first lv,first lq)$%

    eval(p:%,v:SingletonAsOrderedSet,q:%):% == p(q)

    eval(p:%,lv: List SingletonAsOrderedSet,lr: List R):% ==
      empty? lv => p
      not empty? rest lv => error "can only eval a univariate polynomial once"
      eval(p,first lv,first lr)$%
    eval(p:%,v:SingletonAsOrderedSet,r:R):% == p(r)::%

    eval(p:%,le:List Equation %):% ==
      import from Equation %
      import from Partial SingletonAsOrderedSet
      empty? le  => p
      not empty? rest le => error "can only eval a univariate polynomial once"
      failed?(mainVariable(lhs first le)) => p
      p(rhs first le)

    mainVariable(p:%): Partial SingletonAsOrderedSet ==
      zero? degree p =>  failed()
      success(create()$SingletonAsOrderedSet)

    minimumDegree(p:%,v:SingletonAsOrderedSet): NonNegativeInteger == minimumDegree p
    minimumDegree(p:%,lv:List SingletonAsOrderedSet): List NonNegativeInteger ==
       empty? lv => []
       [minimumDegree p]
    monomial(p:%, v:SingletonAsOrderedSet, n:NonNegativeInteger): % ==
       mapExponents((x1: NonNegativeInteger): NonNegativeInteger+->x1+n,p)
    coerce(v:SingletonAsOrderedSet):% == monomial(1$R,1$NonNegativeInteger)
    makeSUP(p): % ==
      zero? p => 0
      monomial(leadingCoefficient p,degree p) + makeSUP reductum p
    unmakeSUP(sp): % ==
      zero? sp => 0
      monomial(leadingCoefficient sp,degree sp) + unmakeSUP reductum sp

    karatsubaDivide(p:%,n:NonNegativeInteger): Record(quotient:%,remainder:%) == monicDivide(p,monomial(1,n))
    shiftRight(p:%,n:NonNegativeInteger): % == monicDivide(p,monomial(1,n)).quotient
    shiftLeft(p:%,n:NonNegativeInteger): % == p * monomial(1,n)

    vectorise(p, n): Vector R ==
      m := minIndex(v := new(n, 0)$Vector(R))
      for i in minIndex v .. maxIndex v repeat
        qsetelt!(v, i, coefficient(p, (i - m)::NonNegativeInteger))
      v
    retract(p:%):R ==
      zero? p => 0
      zero? degree p => leadingCoefficient p
      error "Polynomial is not of degree 0"

    retractIfCan(p:%): Partial R ==
      zero? p => success(0)
      zero? degree p => success(leadingCoefficient p)
      failed()


    differentiate(x:%, deriv:R -> R, xd:%): % ==
      if R has CommutativeRing then
        d:% := 0
        while (dg := degree x) > 0 repeat
          lc := leadingCoefficient x
          d := d + xd * monomial(dg * lc, (dg - 1)::NonNegativeInteger)
                 + monomial(deriv lc, dg)
          x := reductum x
        return d + deriv(leadingCoefficient x)::%
      else
        --local ncdiff: (NonNegativeInteger, %) -> %
        -- computes d(x^n) given dx = xd, non-commutative case
        local ncdiff(n, xd: %): % ==
          zero? n => 0
          zero?(n1 := (n - 1)::NonNegativeInteger) => xd
          xd * monomial(1, n1) + monomial(1, 1) * ncdiff(n1, xd)

        d:% := 0
        while (dg := degree x) > 0 repeat
          lc := leadingCoefficient x
          d := d + monomial(deriv lc, dg) + lc * ncdiff(dg, xd)
          x := reductum x
        return d + deriv(leadingCoefficient x)::%

    differentiate(x:%, deriv:R -> R): % == differentiate(x, deriv, 1$%)$%
    differentiate(x:%): % ==
        d:% := 0
        while (dg := degree x) > 0 repeat
          d := d + monomial(dg * leadingCoefficient x, (dg - 1)::NonNegativeInteger)
          x := reductum x
        d
    differentiate(x:%,v:SingletonAsOrderedSet): % == differentiate x

