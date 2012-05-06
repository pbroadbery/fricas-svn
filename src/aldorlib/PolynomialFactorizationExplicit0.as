--DEPS: UniqueFactorizationDomain
--DEPS: Field UnivariatePolynomialCategoryFunctions2 Fraction_QuotientFieldCategory0
#include "axiom.as"
#pile

P ==> SparseUnivariatePolynomial %

PolynomialFactorizationExplicit0: Category == UniqueFactorizationDomain with
       squareFreePolynomial: P -> Factored(P)
              ++ squareFreePolynomial(p) returns the
              ++ square-free factorization of the
              ++ univariate polynomial p.
       factorPolynomial: P -> Factored(P)
              ++ factorPolynomial(p) returns the factorization
              ++ into irreducibles of the univariate polynomial p.
       factorSquareFreePolynomial: P -> Factored(P)
              ++ factorSquareFreePolynomial(p) factors the
              ++ univariate polynomial p into irreducibles
              ++ where p is known to be square free
              ++ and primitive with respect to its main variable.
       gcdPolynomial: (P, P) -> P
              ++ gcdPolynomial(p,q) returns the gcd of the univariate
              ++ polynomials p qnd q.
              -- defaults to Euclidean, but should be implemented via
              -- modular or p-adic methods.
       solveLinearPolynomialEquation: (List P, P) -> Partial List P
              ++ solveLinearPolynomialEquation([f1, ..., fn], g)
              ++ (where the fi are relatively prime to each other)
              ++ returns a list of ai such that
              ++ \spad{g/prod fi = sum ai/fi}
              ++ or returns "failed" if no such list of ai's exists.
       if % has CharacteristicNonZero then
         conditionP: Matrix % -> Partial(Vector %)
              ++ conditionP(m) returns a vector of elements, not all zero,
              ++ whose \spad{p}-th powers (p is the characteristic of the domain)
              ++ are a solution of the homogenous linear system represented
              ++ by m, or "failed" is there is no such vector.
         charthRoot: % -> Partial %
              ++ charthRoot(r) returns the \spad{p}-th root of r, or "failed"
              ++ if none exists in the domain.
              -- this is a special case of conditionP, but often the one we want
