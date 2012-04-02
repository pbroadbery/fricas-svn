--DEPS: OutputForm SegmentCategory SetCategory SegmentExpansionCategory
--DEPS: Segment_SegmentCategory List_StreamAggregate

#include "axiom.as"

import from Boolean;
import from System;
import from String;

S2(S:Type): SegmentCategory(S) with {
    if S has SetCategory then SetCategory;
    if S has OrderedRing then SegmentExpansionCategory(S, List S);
}
== add {
    import from S;

    if S has SetCategory then {
       coerce(s:%): OutputForm == never;
       (a: %) = (b: %): Boolean == never;
    }

    if S has OrderedRing then {
      expand(ls: List %): List S == never;
      expand(s : %): List S == never;
      map(f : S->S, s : %): List S == never;
    }

 SEGMENT(a: S, b: S) : % == never;
 BY(a: %, b: Integer) : % == never;
 lo(a: %) : S == never;
 hi(a: %) : S == never;
 low(a: %) : S == never;
 high(a: %) : S == never;
 incr(a: %) : Integer == never;
 segment(a: S, b: S) : % == never;
 convert(a: S) : % == never;
 if S has OrderedRing and S has ConvertibleTo(InputForm) then 
		convert(a: %) : InputForm == never;
 if S has ConvertibleTo InputForm then 
		 convert(a: %) : InputForm == never;
} 
