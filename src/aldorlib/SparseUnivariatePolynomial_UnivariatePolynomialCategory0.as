--DEPS: SparseUnivariatePolynomial_FiniteAbelianMonoidRing UnivariatePolynomialCategory0 Integer_IntegralDomain

#include "axiom.as"

import from Boolean;
import from System;
import from String;
#pile

SUP ==> SparseUnivariatePolynomial 

local xunivariate(R: Ring, P: UnivariatePolynomialCategory0 R, p: P): SUP P == 
   	 zero? p => 0
	 lc: P := leadingCoefficient(p)::P
	 d: NonNegativeInteger := degree p;
	 m := monomial(lc, d)
	 r := reductum p
	 u := xunivariate(R, P, p)
	 m + u


local multivariate(R: Ring, P: UnivariatePolynomialCategory0 R)(supp: SUP P, v: SingletonAsOrderedSet): P ==
     import from NonNegativeInteger
     zero? supp => 0
     lc:=leadingCoefficient supp
     degree lc > 0 => error "bad form polynomial"
     monomial(leadingCoefficient lc,degree supp) +
         multivariate(R, P)(reductum supp,v)


extend SparseUnivariatePolynomial(R: Ring): UnivariatePolynomialCategory0(R) with _
 == PolynomialRing(R, NonNegativeInteger) add
--?     	reducedSystem: Matrix(%) -> Matrix(R)
--?		reducedSystem: (Matrix(%), Vector(%)) -> Record(mat: Matrix(R), vec: Vector(R))
--OK	univariate: (%, SingletonAsOrderedSet) -> SparseUnivariatePolynomial(%)
--OK	univariate: % -> SparseUnivariatePolynomial(R)
--OK	multivariate: (SparseUnivariatePolynomial(R), SingletonAsOrderedSet) -> %
--OK	multivariate: (SparseUnivariatePolynomial(%), SingletonAsOrderedSet) -> %
--OK	elt: (%, R) -> R
--OK	elt: (%, %) -> %
--OK	multiplyExponents: (%, NonNegativeInteger) -> %
--OK	divideExponents: (%, NonNegativeInteger) -> Partial(%)
--OK	pseudoRemainder: (%, %) -> %

   Term ==>  Record(k:NonNegativeInteger,c:R)
   Rep ==  List Term
   import from Term, Rep

   local listOfTerms(x: %): List Term == rep(x)

   univariate(p:%,v:SingletonAsOrderedSet): SUP % == xunivariate(R, % pretend UnivariatePolynomialCategory0 R, p)
   --univariate(p:%,v:SingletonAsOrderedSet): SUP % == univariate(%)(p, v)
     --zero? p => 0
     --monomial(leadingCoefficient(p)::%,degree p) +
     --    univariate(reductum p,v)

   univariate(p:%): SUP R == p pretend SparseUnivariatePolynomial(R)

   multivariate(sup:SparseUnivariatePolynomial(R),v:SingletonAsOrderedSet): % ==
      sup pretend %

   multivariate(supp:SparseUnivariatePolynomial(%),v:SingletonAsOrderedSet): % == multivariate(R, % pretend UnivariatePolynomialCategory0 R)(supp, v)
--     zero? supp => 0
--     lc:=leadingCoefficient supp
--     degree lc > 0 => error "bad form polynomial"
--     monomial(leadingCoefficient lc,degree supp) +
--         multivariate(reductum supp,v)

   elt(p:%,val:R): R ==
      import from Integer
      null p => 0$R
      co:=p.first.c
      n:=p.first.k
      for tm in rep(reductum p) repeat
       co:= co * val ^ (n - (n:=tm.k))::NonNegativeInteger + tm.c
      n = 0 => co
      co * val ^ n

   elt(p:%,val:%): % ==
      import from Integer
      null p => 0$%
      coef:% := p.first.c :: %
      n:=p.first.k
      for tm in rep(p).rest repeat
       coef:= coef * val ^ (n-(n:=tm.k))::NonNegativeInteger+(tm.c::%)
      n = 0 => coef
      coef * val ^ n

   multiplyExponents(p: %,n: NonNegativeInteger): % == per [ [u.k*n,u.c] for u in rep p]

   divideExponents(p: %, n: NonNegativeInteger): Partial % ==
     import from Partial Integer
     import from Integer
     null rep p => success(p)
     e := exquo$Integer
     m := (p.first.k :: Integer exquo n::Integer)
     failed? m => failed()
     u:= divideExponents(p.rest,n)
     failed? u => failed()
     success per cons([m::Integer::NonNegativeInteger,p.first.c], rep(u::%))

   local null(x: %): Boolean == null listOfTerms x
   local empty?(x: %): Boolean == null listOfTerms x
   local apply(x: %, zz: 'first'): Term == (listOfTerms x).first
   local apply(x: %, zz: 'rest'): % == per((listOfTerms x).rest)

   import from 'first', 'rest'
   import from Term

   pseudoRemainder(p1: %, p2: %): % ==
     import from Partial NonNegativeInteger
     import from Partial Integer
     import from Integer
     null p2 => error "PseudoDivision by Zero"
     null p1 => 0
     co := p2.first.c
     e := p2.first.k
     p2 := p2.rest
     kk := (p1.first.k)
     e1:=max(kk-e+1,0)::NonNegativeInteger
     while not null p1 repeat
       if failed?(u := subtractIfCan(p1.first.k, e)) then break
       p1:=fmecg(co * p1.rest, u::NonNegativeInteger, p1.first.c, p2)
       e1:= (e1 - 1)::NonNegativeInteger
     e1 = 0 => p1
     co ^ e1 * p1
