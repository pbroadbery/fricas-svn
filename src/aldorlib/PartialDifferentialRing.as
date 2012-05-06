--DEPS: Ring init_Symbol List NonNegativeInteger Segment_SegmentCategory
#include "axiom.as"

import from Boolean;

PartialDifferentialRing(S:SetCategory): Category == Ring with {
    differentiate: (%, S) -> %;
        ++ differentiate(x,v) computes the partial derivative of x
        ++ with respect to v.
    differentiate: (%, List S) -> %;
        ++ differentiate(x,[s1,...sn]) computes successive partial derivatives,
        ++ i.e. \spad{differentiate(...differentiate(x, s1)..., sn)}.
    differentiate: (%, S, NonNegativeInteger) -> %;
        ++ differentiate(x, s, n) computes multiple partial derivatives, i.e.
        ++ n-th derivative of x with respect to s.
    differentiate: (%, List S, List NonNegativeInteger) -> %;
        ++ differentiate(x, [s1,...,sn], [n1,...,nn]) computes
        ++ multiple partial derivatives, i.e.
    D: (%, S) -> %;
        ++ D(x,v) computes the partial derivative of x
        ++ with respect to v.
    D: (%, List S) -> %;
        ++ D(x,[s1,...sn]) computes successive partial derivatives,
        ++ i.e. \spad{D(...D(x, s1)..., sn)}.
    D: (%, S, NonNegativeInteger) -> %;
        ++ D(x, s, n) computes multiple partial derivatives, i.e.
        ++ n-th derivative of x with respect to s.
    D: (%, List S, List NonNegativeInteger) -> %;
        ++ D(x, [s1,...,sn], [n1,...,nn]) computes
        ++ multiple partial derivatives, i.e.
        ++ \spad{D(...D(x, s1, n1)..., sn, nn)}.
  default {
    import from Segment NonNegativeInteger;
    differentiate(r:%, l:List S): % == {
      for s in l repeat r := differentiate(r, s);
      r}

    differentiate(r:%, s:S, n:NonNegativeInteger): % == {
      for i in 1..n repeat r := differentiate(r, s);
      r}

    differentiate(r:%, ls:List S, ln:List NonNegativeInteger): % == {
      for s in ls for n in ln repeat r := differentiate(r, s, n);
      r}

    D(r:%, v:S): % == differentiate(r,v);
    D(r:%, lv:List S): % == differentiate(r,lv);
    D(r:%, v:S, n:NonNegativeInteger): % == differentiate(r,v,n);
    D(r:%, lv:List S, ln:List NonNegativeInteger): % == differentiate(r, lv, ln);
}
}