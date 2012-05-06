--DEPS:  OrderedRing StreamAggregate SegmentCategory
#include "axiom.as"

import from Boolean;

SegmentExpansionCategory(S: OrderedRing, L: StreamAggregate(S)): Category ==
    SegmentCategory(S) with {
      expand: List % -> L;
        ++ expand(l) creates a new value of type L in which each segment
        ++ \spad{l..h by k} is replaced with \spad{l, l+k, ... lN},
        ++ where \spad{lN <= h < lN+k}.
        ++ For example, \spad{expand [1..4, 7..9] = [1,2,3,4,7,8,9]}.
      expand: % -> L;
        ++ expand(l..h by k) creates value of type L with elements
        ++ \spad{l, l+k, ... lN} where \spad{lN <= h < lN+k}.
        ++ For example, \spad{expand(1..5 by 2) = [1,3,5]}.
      map: (S -> S, %) -> L;
        ++ map(f,l..h by k) produces a value of type L by applying f
        ++ to each of the succesive elements of the segment, that is,
        ++ \spad{[f(l), f(l+k), ..., f(lN)]}, where \spad{lN <= h < lN+k}.
}
