--DEPS: Integer_IntegralDomain Fraction_DivisionRing

#include "axiom.as"
#pile

RadicalCategory: Category == with
  sqrt   : % -> %
      ++ sqrt(x) returns the square root of x.  The branch cut lies along the
      ++ negative real axis, continuous with quadrant II.
  nthRoot: (%, Integer) -> %
      ++ nthRoot(x,n) returns the nth root of x.
  _^     : (%, Fraction Integer) -> %
      ++ x ^ y is the rational exponentiation of x by the power y.
  default
    default x: %
    default n: Integer
    import from Fraction Integer
    sqrt(x): %       == x ^ inv(2::Fraction(Integer))
    nthRoot(x, n): % == x ^ inv(n::Fraction(Integer))
