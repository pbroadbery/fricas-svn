--DEPS: Fraction_DivisionRing QuotientFieldCategory0 CommonDenominator 
--DEPS: Matrix_MatrixCategory PolynomialFactorizationExplicit0
#include "axiom.as"
#pile

QuotientFieldCategory1(S: IntegralDomain): Category == Join(QuotientFieldCategory0 S, FullyLinearlyExplicitRingOver S) with
    if S has PolynomialFactorizationExplicit0 then
      PolynomialFactorizationExplicit0
