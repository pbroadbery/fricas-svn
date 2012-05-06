--DEPS: Ring NonNegativeInteger Segment_SegmentCategory
#include "axiom.as"

DifferentialRing: Category == Ring with {
    differentiate: % -> %;
         ++ differentiate(x) returns the derivative of x.
         ++ This function is a simple differential operator
         ++ where no variable needs to be specified.
    D: % -> %;
         ++ D(x) returns the derivative of x.
         ++ This function is a simple differential operator
         ++ where no variable needs to be specified.
    differentiate: (%, NonNegativeInteger) -> %;
         ++ differentiate(x, n) returns the n-th derivative of x.
    D: (%, NonNegativeInteger) -> %;
         ++ D(x, n) returns the n-th derivative of x.
  default {
    default r: %;
    default n: NonNegativeInteger;

    D r: % == differentiate r;
    differentiate(r, n): % == {
      import from Segment NonNegativeInteger;
      for i in 1..n repeat r := differentiate r;
      r}
    D(r,n): % == differentiate(r,n);
}
}