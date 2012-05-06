--DEPS: SparseUnivariatePolynomial_UnivariatePolynomialCategory0 PseudoRemainderSequence
#include "axiom.as"
#pile
import from Boolean

extend SparseUnivariatePolynomial(R: Ring): UnivariatePolynomialCategory0(R) with 
   if R has IntegralDomain then 
      resultant: (%, %) -> R
      discriminant: % -> R
      subResultantGcd: (%, %) -> %
 == add

   if R has IntegralDomain then
     resultant(p1: %, p2: %): R == resultant(p1,p2)$PseudoRemainderSequence(R,%)
     discriminant(p: %): R == discriminant(p)$PseudoRemainderSequence(R,%)
     subResultantGcd(p1: %, p2: %): % == subResultantGcd(p1,p2)$PseudoRemainderSequence(R,%)
