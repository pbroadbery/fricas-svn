--DEPS: GcdDomain0 SparseUnivariatePolynomial_R
#include "axiom.as"

#pile
import from Boolean

-- This needs 'subResultantGcd' from SUP %, which pulls in the full definition
-- of SUP

GcdDomain: Category == GcdDomain0 
 with 
    gcdPolynomial: (SparseUnivariatePolynomial %, SparseUnivariatePolynomial %) ->
           SparseUnivariatePolynomial %;
            ++ gcdPolynomial(p,q) returns the greatest common divisor (gcd) of
            ++ univariate polynomials over the domain
    default  
      SUP ==> SparseUnivariatePolynomial
      default p1, p2: SUP %

      gcdPolynomial(p1,p2): SUP % ==
        import from NonNegativeInteger
        import from Partial SUP %
        zero? p1 => unitCanonical p2
        zero? p2 => unitCanonical p1
        c1:= content(p1); c2:= content(p2)
        p1:= (p1 exquo c1)::SUP %
        p2:= (p2 exquo c2)::SUP %
        if (e1:=minimumDegree p1) > 0 then p1:=(p1 exquo monomial(1,e1))::SUP %
        if (e2:=minimumDegree p2) > 0 then p2:=(p2 exquo monomial(1,e2))::SUP %
        e1:=min(e1,e2); c1:=gcd(c1,c2)
        p1:=
           degree p1 = 0 or degree p2 = 0 => monomial(c1,0)
           p:= subResultantGcd(p1,p2)
           degree p = 0 => monomial(c1,0)
           c2:= gcd(leadingCoefficient p1,leadingCoefficient p2)
           unitCanonical(c1 * primitivePart(((c2*p) exquo leadingCoefficient p)::SUP %))
        zero? e1 => p1
        monomial(1,e1)*p1
