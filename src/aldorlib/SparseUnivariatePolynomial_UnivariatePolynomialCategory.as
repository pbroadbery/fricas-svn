--DEPS:SparseUnivariatePolynomial_R UnivariatePolynomialCategory
#include "axiom.as"
#pile

extend SparseUnivariatePolynomial(R: Ring): UnivariatePolynomialCategory R with 
== add

--    if R has GcdDomain0 then
--        separate: (%, %) -> Record(primePart: %, commonPart: %)
--        squareFreePart: % -> %
--    if R has IntegralDomain  and % has shallowlyMutablethen
--        set!: (%, Fraction(%), Fraction(%)) -> Fraction(%)
--    if R has StepThrough then
--        nextItem: % -> Partial(%)
