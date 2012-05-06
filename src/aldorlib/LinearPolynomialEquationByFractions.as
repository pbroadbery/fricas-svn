--DEPS: PolynomialFactorizationExplicit0 SparseUnivariatePolynomial_UnivariatePolynomialCategory
--DEPS: Fraction_QuotientFieldCategory1
#include "axiom.as"
#pile

LinearPolynomialEquationByFractions(R: PolynomialFactorizationExplicit0): with
  solveLinearPolynomialEquationByFractions: ( _
           List SparseUnivariatePolynomial R, _
           SparseUnivariatePolynomial R) ->   _
           Partial(List SparseUnivariatePolynomial R)
        ++ solveLinearPolynomialEquationByFractions([f1, ..., fn], g)
        ++ (where the fi are relatively prime to each other)
        ++ returns a list of ai such that
        ++ \spad{g/prod fi = sum ai/fi}
        ++ or returns "failed" if no such exists.
 == add
  SupR ==> SparseUnivariatePolynomial R
  F ==> Fraction R
  SupF ==> SparseUnivariatePolynomial F
  import from UnivariatePolynomialCategoryFunctions2(R,SupR,F,SupF)
  import from F
  default lp : List SupR
  default pp: SupR
  default pF: SupF
--  pullback : SupF -> Union(SupR,"failed")

  local pullback(pF: SupF): Partial SupR ==
    pF = 0 => [0]
    c: Partial R :=retractIfCan leadingCoefficient pF
    c case failed => [failed]
    r := pullback reductum pF
    r case failed => [failed]
    [monomial(c::R,degree pF) + r::SupR]

  solveLinearPolynomialEquationByFractions(lp,pp): Partial List SparseUnivariatePolynomial R ==
    import from Partial SupF
    lpF : List SupF := [map((x : R) : F +-> x::F, u) for u in lp]
    pF : SupF := map((x : R) : F +-> x::F, pp)
    ans: Partial List SupF := solveLinearPolynomialEquation(lpF,pF)$F
    ans case failed => [failed]
    [pullback v for v in coerce ans]


