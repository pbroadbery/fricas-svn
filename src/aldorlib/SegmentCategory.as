--DEPS:  ConvertibleTo init_InputForm Integer init_Generator
#include "axiom.as"

import from Boolean;

SegmentCategory(S:Type): Category == with {
    SEGMENT: (S, S) -> %;
        ++ \spad{l..h} creates a segment with l and h as the endpoints.
    BY: (%, Integer) -> %;
        ++ \spad{s by n} creates a new segment in which only every \spad{n}-th
        ++ element is used.
    by: (%, Integer) -> %;
        ++ \spad{s by n} creates a new segment in which only every \spad{n}-th
        ++ element is used.
    lo: % -> S;
        ++ lo(s) returns the first endpoint of s.
        ++ Note: \spad{lo(l..h) = l}.
    hi: % -> S;
        ++ hi(s) returns the second endpoint of s.
        ++ Note: \spad{hi(l..h) = h}.
    low: % -> S;
        ++ low(s) returns the first endpoint of s.
        ++ Note: \spad{low(l..h) = l}.
    high: % -> S;
        ++ high(s) returns the second endpoint of s.
        ++ Note: \spad{high(l..h) = h}.
    incr: % -> Integer;
        ++ incr(s) returns \spad{n}, where s is a segment in which every
        ++ \spad{n}-th element is used.
        ++ Note: \spad{incr(l..h by n) = n}.
    segment: (S, S) -> %;
        ++ segment(i,j) is an alternate way to create the segment \spad{i..j}.
    convert: S -> %;
        ++ convert(i) creates the segment \spad{i..i}.

    if S has ConvertibleTo InputForm then ConvertibleTo InputForm;

    default {
      (s: %) by (n: Integer): % == BY(s, n)
    }
    
}