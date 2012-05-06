--DEPS: PolynomialRing NonNegativeInteger_OrderedAbelianMonoidSup init_SparseUnivariatePolynomial
#include "axiom.as"

#pile
import from Boolean
import from System
import from String

extend SparseUnivariatePolynomial(R:Ring): FiniteAbelianMonoidRing(R, NonNegativeInteger) with 
  monicDivide : (%,%) -> Record(quotient:%,remainder:%)
  0: %
  1: %
  fmecg: (%, NonNegativeInteger, R, %) -> %
== PolynomialRing(R, NonNegativeInteger) add
    import from Record(quotient:%,remainder:%)
    import from R, NonNegativeInteger
    Term ==>  Record(k:NonNegativeInteger, c:R)
    Rep ==  List Term
    import from Term
    import from Rep

    0: % == per [];
    1: % == monomial(1, 0)

    monicDivide(p1:%, p2:%): Record(quotient:%,remainder:%) ==
      import from Partial NonNegativeInteger
      null  rep(p2) => error "monicDivide: division by 0"
      leadingCoefficient p2 ~= 1 => error "Divisor Not Monic"
      p2 = 1$% => [p1,0$%]
      null rep(p1) => [0$%,0$%]
      degree p1 < (n:=degree p2) => [0$%,p1]
      rout:Rep := []
      rp2 := rep(p2).rest
      while not null rep(p1) repeat
         failed?(u := subtractIfCan(rep(p1).first.k, n)) => break
         rout:= cons([(u)::NonNegativeInteger, rep(p1).first.c], rout)
         p1 := fmecg(per(rep(p1).rest), rout.first.k, rout.first.c, per rp2)
      [per reverse!(rout),p1]

