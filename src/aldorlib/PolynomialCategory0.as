--DEPS: OrderedAbelianMonoidSup PartialDifferentialRing FiniteAbelianMonoidRing InnerEvalable Evalable
--DEPS: FullyLinearlyExplicitRingOver SparseUnivariatePolynomial_FiniteAbelianMonoidRing
--DEPS: Equation_SetCategory
#include "axiom.as"
#pile

import from Boolean
import from System
import from String

-- As polynomialcategory but without the conditionals
PolynomialCategory0(R:Ring, E:OrderedAbelianMonoidSup, VarSet:OrderedSet):
        Category ==
  Join(PartialDifferentialRing VarSet, FiniteAbelianMonoidRing(R, E),
       Evalable %, InnerEvalable(VarSet, R),
       InnerEvalable(VarSet, %), RetractableTo VarSet
       ) with
    -- operations
   degree : (%,VarSet) -> NonNegativeInteger
     ++ degree(p,v) gives the degree of polynomial p with respect to the variable v.
   degree : (%,List(VarSet)) -> List(NonNegativeInteger)
     ++ degree(p,lv) gives the list of degrees of polynomial p
     ++ with respect to each of the variables in the list lv.
   coefficient: (%,VarSet,NonNegativeInteger) -> %
     ++ coefficient(p,v,n) views the polynomial p as a univariate
     ++ polynomial in v and returns the coefficient of the \spad{v^n} term.
   coefficient: (%,List VarSet,List NonNegativeInteger) -> %
     ++ coefficient(p, lv, ln) views the polynomial p as a polynomial
     ++ in the variables of lv and returns the coefficient of the term
     ++ \spad{lv^ln}, i.e. \spad{prod(lv_i ^ ln_i)}.
   monomials: % -> List %
     ++ monomials(p) returns the list of non-zero monomials of polynomial p, i.e.
     ++ \spad{monomials(sum(a_(i) X^(i))) = [a_(1) X^(1),...,a_(n) X^(n)]}.
   univariate   : (%,VarSet) -> SparseUnivariatePolynomial(%)
     ++ univariate(p,v) converts the multivariate polynomial p
     ++ into a univariate polynomial in v, whose coefficients are still
     ++ multivariate polynomials (in all the other variables).
   univariate   : % -> SparseUnivariatePolynomial(R)
       ++ univariate(p) converts the multivariate polynomial p,
       ++ which should actually involve only one variable,
       ++ into a univariate polynomial
       ++ in that variable, whose coefficients are in the ground ring.
       ++ Error: if polynomial is genuinely multivariate
   mainVariable  : % -> Partial VarSet
          ++ mainVariable(p) returns the biggest variable which actually
          ++ occurs in the polynomial p, or "failed" if no variables are
          ++ present.
          ++ fails precisely if polynomial satisfies ground?
   minimumDegree : (%,VarSet) -> NonNegativeInteger
     ++ minimumDegree(p,v) gives the minimum degree of polynomial p
     ++ with respect to v, i.e. viewed a univariate polynomial in v
   minimumDegree : (%,List(VarSet)) -> List(NonNegativeInteger)
     ++ minimumDegree(p, lv) gives the list of minimum degrees of the
     ++ polynomial p with respect to each of the variables in the list lv
   monicDivide : (%,%,VarSet) -> Record(quotient:%,remainder:%)
      ++ monicDivide(a,b,v) divides the polynomial a by the polynomial b,
      ++ with each viewed as a univariate polynomial in v returning
      ++ both the quotient and remainder.
      ++ Error: if b is not monic with respect to v.
   monomial : (%,VarSet,NonNegativeInteger) -> %
       ++ monomial(a,x,n) creates the monomial \spad{a*x^n} where \spad{a} is
       ++ a polynomial, x is a variable and n is a nonnegative integer.
   monomial : (%,List VarSet,List NonNegativeInteger) -> %
       ++ monomial(a,[v1..vn],[e1..en]) returns \spad{a*prod(vi^ei)}.
   multivariate : (SparseUnivariatePolynomial(R),VarSet) -> %
       ++ multivariate(sup,v) converts an anonymous univariable
       ++ polynomial sup to a polynomial in the variable v.
   multivariate : (SparseUnivariatePolynomial(%),VarSet) -> %
       ++ multivariate(sup,v) converts an anonymous univariable
       ++ polynomial sup to a polynomial in the variable v.
   isPlus: % -> Partial List %
       ++ isPlus(p) returns \spad{[m1,...,mn]} if polynomial \spad{p = m1 + ... + mn} and
       ++ \spad{n >= 2} and each mi is a nonzero monomial.
   isTimes: % -> Partial List %
       ++ isTimes(p) returns \spad{[a1,...,an]} if polynomial \spad{p = a1 ... an}
       ++ and \spad{n >= 2}, and, for each i, ai is either a nontrivial constant in R or else of the
       ++ form \spad{x^e}, where \spad{e > 0} is an integer and x in a member of VarSet.
   isExpt: % -> Partial(Record(var:VarSet, exponent:NonNegativeInteger))
       ++ isExpt(p) returns \spad{[x, n]} if polynomial p has the form \spad{x^n} and \spad{n > 0}.
   totalDegree : % -> NonNegativeInteger
       ++ totalDegree(p) returns the largest sum over all monomials
       ++ of all exponents of a monomial.
   totalDegree : (%,List VarSet) -> NonNegativeInteger
       ++ totalDegree(p, lv) returns the maximum sum (over all monomials of polynomial p)
       ++ of the variables in the list lv.
   totalDegreeSorted : (%, List VarSet) -> NonNegativeInteger
       ++ totalDegreeSorted(p, lv) returns the maximum sum (over all
       ++ monomials of polynomial p) of the degree in variables in the
       ++ list lv.  lv is assumed to be sorted in decreasing order.
   variables : % -> List(VarSet)
       ++ variables(p) returns the list of those variables actually
       ++ appearing in the polynomial p.
   primitiveMonomials: % -> List %
       ++ primitiveMonomials(p) gives the list of monomials of the
       ++ polynomial p with their coefficients removed.
       ++ Note: \spad{primitiveMonomials(sum(a_(i) X^(i))) = [X^(1),...,X^(n)]}.
   default
    import from R
    default p, p1, p2:%
    default v:VarSet
    default ln:List NonNegativeInteger
    default lv:List VarSet
    default n:NonNegativeInteger
    default pp,qq:SparseUnivariatePolynomial %
    default mvar: VarSet

    eval(p:%, l:List Equation %): % ==
      import from Partial VarSet
      import from Equation %
      empty? l => p
      for e in l repeat
        failed?(retractIfCan(lhs e)@Partial VarSet) =>
             error "cannot find a variable to evaluate"
      lvar:=[retract(lhs e)@VarSet for e in l]
      eval(p, lvar,[rhs e for e in l]$List(%))

    monomials p: List % ==
--    zero? p => empty()
--    concat(leadingMonomial p, monomials reductum p)
--    replaced by sequential version for efficiency, by WMSIT, 7/30/90
      ml:= empty()$List(%)
      while p ~= 0 repeat
        ml:=concat(leadingMonomial p, ml)
        p:= reductum p
      reverse ml

    isPlus p: Partial List % ==
      import from List %
      empty? rest(l := monomials p) => failed()
      success(l)

    isTimes p: Partial List % ==
      import from List %, R
      empty?(lv := variables p) or not monomial? p => failed()
      l := [monomial(1, v, degree(p, v)) for v in lv]
--      one?(r := leadingCoefficient p) =>
      ((r := leadingCoefficient p) = 1) =>
        empty? rest lv => failed()
        success(l)
      success(concat(r::%, l))

    isExpt p: Partial Record(var: VarSet, exponent: NonNegativeInteger) ==
      import from Record(var: VarSet, exponent: NonNegativeInteger)
      import from Partial VarSet
      failed?(u := mainVariable p) => failed()
      p = monomial(1, u::VarSet, d := degree(p, u::VarSet)) =>
        success([u::VarSet, d])
      failed()

    coefficient(p,v,n): % == coefficient(univariate(p,v),n)
    coefficient(p,lv,ln): % ==
       empty? lv =>
         empty? ln => p
         error "mismatched lists in coefficient"
       empty? ln  => error "mismatched lists in coefficient"
       coefficient(coefficient(univariate(p,first lv),first ln),
                   rest lv,rest ln)
    monomial(p,lv,ln): % ==
       empty? lv =>
         empty? ln => p
         error "mismatched lists in monomial"
       empty? ln  => error "mismatched lists in monomial"
       monomial(monomial(p,first lv, first ln),rest lv, rest ln)

    retract(p:%):VarSet ==
      import from Partial VarSet
      q := mainVariable(p)::VarSet
      q::% = p => q
      error "Polynomial is not a single variable"

    retractIfCan(p:%): Partial VarSet ==
      success?(q := mainVariable p) and (q::VarSet::% = p) => q
      failed()

    mkPrim(p:%):% == monomial(1,degree p)
    primitiveMonomials p: List % == [mkPrim q for q in monomials p]
    totalDegree p: NonNegativeInteger ==
        import from Partial VarSet
        ground? p => 0
        u := univariate(p, mainVariable(p)::VarSet)
        d: NonNegativeInteger := 0
        while u ~= 0 repeat
          d := max(d, degree u + totalDegree leadingCoefficient u)
          u := reductum u
        d

    totalDegreeSorted(p : %, lv : List VarSet) : NonNegativeInteger ==
        import from Partial VarSet
        ground? p => 0
        empty?(lv) => 0
        u := univariate(p, v:=(mainVariable(p)::VarSet))
        d: NonNegativeInteger := 0
        w: NonNegativeInteger := 0
        v0 := first(lv)
        lv := rest(lv)
        while not(empty?(lv)) and v < v0 repeat
            v0 := first(lv)
            lv := rest(lv)
        if v0 = v then w := 1
        while u ~= 0 repeat
          d := max(d, w*(degree u) +
                 totalDegreeSorted(leadingCoefficient u, lv))
          u := reductum u
        d

    totalDegree(p,lv): NonNegativeInteger ==
        lv1 := sort((v1 : VarSet, v2 : VarSet) : Boolean +-> v2 < v1, lv)
        totalDegreeSorted(p, lv1)


    monicDivide(p1,p2,mvar): Record(quotient:%,remainder:%) ==
       import from SparseUnivariatePolynomial %
       import from Record(quotient: SparseUnivariatePolynomial %, remainder: SparseUnivariatePolynomial %)
       result := monicDivide(univariate(p1,mvar),univariate(p2,mvar))
       [multivariate(result.quotient,mvar),
        multivariate(result.remainder,mvar)]


