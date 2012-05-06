--DEPS: GcdDomain Factored_Base
#include "axiom.as"
#pile
UniqueFactorizationDomain: Category == GcdDomain with 
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
 default 
  fUnion ==> 'nil,sqfr,irred,prime'
  FF     ==> Record(flg: fUnion, fctr: %, xpnt: Integer)
  import from List FF
  import from Factored %
  import from NonNegativeInteger

  squareFreePart(x: %): % ==
    import from List RFE %
    import from Fold %
    import from List %
    s := squareFree x
    unit(s) * ((*)/[f.factor for f in factors s])

  prime?(x: %): Boolean == # factorList factor x = 1;

