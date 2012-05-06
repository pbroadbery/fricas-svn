--DEPS: UnivariatePolynomialCategory0 PolynomialCategory StepThrough 
--DEPS: additiveValuation EuclideanDomain0 Fraction_DivisionRing
#include "axiom"

import from Boolean;
import from System;
import from String;

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

UnivariatePolynomialCategory(R:Ring): Category == Join(UnivariatePolynomialCategory0(R), PolynomialCategory(R, NonNegativeInteger, SingletonAsOrderedSet)) with
   if R has StepThrough then StepThrough
   if R has CommutativeRing then
     discriminant: % -> R
       ++ discriminant(p) returns the discriminant of the polynomial p.
     resultant: (%,%) -> R
       ++ resultant(p,q) returns the resultant of the polynomials p and q.
   if R has IntegralDomain then
       Eltable(Fraction %, Fraction %)
       elt  : (Fraction %, Fraction %) -> Fraction %
            ++ elt(a,b) evaluates the fraction of univariate polynomials \spad{a}
            ++ with the distinguished variable replaced by b.
       order: (%, %) -> NonNegativeInteger
            ++ order(p, q) returns the largest n such that \spad{q^n} divides polynomial p
            ++ i.e. the order of \spad{p(x)} at \spad{q(x)=0}.
       subResultantGcd: (%,%) -> %
          ++ subResultantGcd(p,q) computes the gcd of the polynomials p and q
          ++ using the SubResultant GCD algorithm.
       composite: (%, %) -> Partial %
          ++ composite(p, q) returns h if \spad{p = h(q)}, and "failed" no such h exists.
       composite: (Fraction %, %) -> Partial Fraction %
          ++ composite(f, q) returns h if f = h(q), and "failed" is no such h exists.
       pseudoQuotient: (%,%) -> %
          ++ pseudoQuotient(p,q) returns r, the quotient when
          ++ \spad{p' := p*lc(q)^(deg p - deg q + 1)}
          ++ is pseudo right-divided by q, i.e. \spad{p' = s q + r}.
       pseudoDivide: (%, %) -> Record(coef:R, quotient: %, remainder:%)
          ++ pseudoDivide(p,q) returns \spad{[c, q, r]}, when
          ++ \spad{p' := p*lc(q)^(deg p - deg q + 1) = c * p}
          ++ is pseudo right-divided by q, i.e. \spad{p' = s q + r}.
   if R has GcdDomain0 then
       separate: (%, %) -> Record(primePart:%, commonPart: %)
          ++ separate(p, q) returns \spad{[a, b]} such that polynomial \spad{p = a b} and
          ++ \spad{a} is relatively prime to q.
   if R has Field0 then
       EuclideanDomain0
       additiveValuation
         ++ euclideanSize(a*b) = euclideanSize(a) + euclideanSize(b)
       elt      : (Fraction %, R) -> R
           ++ elt(a,r) evaluates the fraction of univariate polynomials \spad{a}
           ++ with the distinguished variable replaced by the constant r.
   if R has Algebra Fraction Integer then
     integrate: % -> %
       ++ integrate(p) integrates the univariate polynomial p with respect
       ++ to its distinguished variable.
   default
    default pp,qq: SparseUnivariatePolynomial %
    default p, q, sp: %
    default n: NonNegativeInteger
    import from Record(coef:R, quotient: %, remainder:%)
    import from Partial %
    import from Partial R
    import from R
    import from Integer
    
--    if R has PolynomialFactorizationExplicit then
--       PFBRU ==>PolynomialFactorizationByRecursionUnivariate(R,%)
--       default pp,qq:SparseUnivariatePolynomial %
--       default lpp:List SparseUnivariatePolynomial %
--       SupR ==> SparseUnivariatePolynomial R
--       default sp:SupR
--
--       solveLinearPolynomialEquation(lpp,pp) ==
--         solveLinearPolynomialEquationByRecursion(lpp,pp)$PFBRU
--       factorPolynomial(pp) ==
--         factorByRecursion(pp)$PFBRU
--       factorSquareFreePolynomial(pp) ==
--         factorSquareFreeByRecursion(pp)$PFBRU
--
--       import from FactoredFunctions2(SupR,S)
--       factor p ==
--         zero? degree p  =>
--           ansR:=factor leadingCoefficient p
--           makeFR(unit(ansR)::%,
--                  [[w.flg,w.fctr::%,w.xpnt] for w in factorList ansR])
--         map(unmakeSUP,factorPolynomial(makeSUP p)$R)

    if R has StepThrough then
       init(): % == init()$R::%
       nextItemInner: % -> Partial %

       nextItemInner(p: %): Partial % ==
         zero? p => success(nextItem(0$R)::R::%) -- assumed not to fail
         zero? degree p =>
           nn:=nextItem leadingCoefficient p
           failed? nn => failed()
           success(nn::R::%)
         n1:=reductum p
         n2:=nextItemInner n1 -- try stepping the reductum
         success? n2 => success(monomial(leadingCoefficient p,degree p) + n2::%)
         1+degree n1 < degree p => -- there was a hole between lt n and n1
           success(monomial(leadingCoefficient p, degree p)+
                    monomial(nextItem(init()$R)::R,1+degree n1))
         n3:=nextItem leadingCoefficient p
         failed? n3 => failed()
         success(monomial(n3::R, degree p))

       nextItem(p: %): Partial % ==
         n1:=nextItemInner p
         failed? n1 => success(monomial(nextItem(init()$R)::R,1+degree(p)))
         success(n1::%)

    if R has GcdDomain0 then

      content(p:%,v:SingletonAsOrderedSet): % == content(p)::%

      --primeFactor: (%, %) -> %

      local primeFactor(p, q): % ==
        --(p1 := (p exquo gcd(p, q))::%) = p => p
	g := gcd(p, q)
	(p1 := (p exquo g)::%) = p => p
        primeFactor(p1, q)

      separate(p, q): Record(primePart: %, commonPart: %) ==
        a := primeFactor(p, q)
        [a, (p exquo a)::%]


    if R has IntegralDomain then
      elt(g:Fraction %, f:Fraction %): Fraction % == 
        ((numer g) f) / ((denom g) f)

      pseudoQuotient(p, q): % ==
        (nn: Integer := degree(p) - degree q + 1) < 1 => 0
        ((leadingCoefficient(q)^(nn::NonNegativeInteger) * p
          - pseudoRemainder(p, q)) exquo q)::%

      pseudoDivide(p, q): Record(coef:R, quotient: %, remainder:%) ==
        (nn := degree(p) - degree q + 1) < 1 => [1, 0, p]
        prem := pseudoRemainder(p, q)
        lc   := leadingCoefficient(q)^(nn::NonNegativeInteger)
        [lc,((lc*p - prem) exquo q)::%, prem]

      composite(f:Fraction %, q:%): Partial Fraction % ==
        failed?(c := composite(numer f, q)) => failed()
        failed?(d := composite(denom f, q)) => failed()
        success(c::% / d::%)

      composite(p:%, q:%): Partial % ==
        ground? p => success(p)
        cqr := pseudoDivide(p, q)
        ground?(cqr.remainder) and
          success?((v := cqr.remainder exquo cqr.coef)) and
            success?(u := composite(cqr.quotient, q)) and
              success?((w := (u::%) exquo cqr.coef)) =>
                success(v::% + monomial(1, 1) * w::%)
        failed()

      apply(p:%, f:Fraction %): Fraction % == elt(p, f)
      elt(p:%, f:Fraction %): Fraction % ==
        zero? p => 0
        ans:Fraction(%) := (leadingCoefficient p)::%::Fraction(%)
        n := degree p
        while not zero?(p:=reductum p) repeat
          ans := ans * f ^ (n - (n := degree p))::NonNegativeInteger +
                    (leadingCoefficient p)::%::Fraction(%)
        zero? n => ans
        ans * f ^ n

      order(p, q): NonNegativeInteger ==
        zero? p => error "order: arguments must be nonzero"
        degree(q) < 1 => error "order: place must be non-trivial"
        ans:NonNegativeInteger := 0
        repeat
          failed?(u  := p exquo q) => return ans
          p   := u::%
          ans := ans + 1

--    if R has GcdDomain then
--      squareFree(p:%) ==
--        squareFree(p)$UnivariatePolynomialSquareFree(R, %)
--
--      squareFreePart(p:%) ==
--        squareFreePart(p)$UnivariatePolynomialSquareFree(R, %)

--    if R has PolynomialFactorizationExplicit then
--
--      gcdPolynomial(pp,qq) ==
--            zero? pp => unitCanonical qq  -- subResultantGcd can't handle 0
--            zero? qq => unitCanonical pp
--            unitCanonical(gcd(content (pp),content(qq)) * primitivePart subResultantGcd(primitivePart pp,primitivePart qq))
--
--      squareFreePolynomial pp ==
--         squareFree(pp)$UnivariatePolynomialSquareFree(%,
--                                    SparseUnivariatePolynomial %)

    if R has Field0 then
      elt(f:Fraction %, r:R): R == ((numer f) r) / ((denom f) r)

      euclideanSize(x: %): NonNegativeInteger ==
            zero? x =>
              error "euclideanSize called on 0 in Univariate Polynomial"
            degree x
      divide(x: %, y: %): Record(quotient: %, remainder:%) ==
            zero? y => error "division by 0 in Univariate Polynomials"
            quot: % :=0
            lc := inv leadingCoefficient y
            while not zero?(x) and (degree x >= degree y) repeat
               f:=lc*leadingCoefficient x
               n:=(degree x - degree y)::NonNegativeInteger
               quot:=quot+monomial(f,n)
               x:=x-monomial(f,n)*y
            [quot,x]

    if R has Algebra Fraction Integer then
      integrate p: % ==
        import from Fraction Integer
        ans:% := 0
        while p ~= 0 repeat
          l := leadingCoefficient p
          d := 1 + degree p
          ans := ans + inv(d::Integer::Fraction(Integer)) * monomial(l, d)
          p := reductum p
        ans
