--DEPS: GcdDomain Factored
#include "axiom.as"

UniqueFactorizationDomain(): Category == GcdDomain with {
    --operations
      prime?: % -> Boolean;
            ++ prime?(x) tests if x can never be written as the product of two
            ++ non-units of the ring,
            ++ i.e., x is an irreducible element.
      squareFree    : % -> Factored(%);
            ++ squareFree(x) returns the square-free factorization of x
            ++ i.e. such that the factors are pairwise relatively prime
            ++ and each has multiple prime factors.
      squareFreePart: % -> %;
            ++ squareFreePart(x) returns a product of prime factors of
            ++ x each taken with multiplicity one.
      factor: % -> Factored(%);
            ++ factor(x) returns the factorization of x into irreducibles.
 default {
  squareFreePart x ==
    unit(s := squareFree x) * _*/[f.factor for f in factors s];

  prime? x == # factorList factor x = 1;

}