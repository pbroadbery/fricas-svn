--DEPS: OutputForm SegmentCategory SetCategory SegmentExpansionCategory
--DEPS: Segment_SegmentCategory List_StreamAggregate

#include "axiom.as"

import from Boolean;
import from System;
import from String;

extend Segment(S:Type): SegmentCategory(S) with {
    if S has SetCategory then SetCategory;
    if S has OrderedRing then SegmentExpansionCategory(S, List S);
}
== add {
    import from S;
    import from List S;

    if S has SetCategory then {
       coerce(s:%): OutputForm == never;
       (a: %) = (b: %): Boolean == never;
    }

    if S has OrderedRing then {
      expand(ls: List %): List S == never;
      expand(s : %): List S == never;
      map(f : S->S, s : %): List S == never;
    }

} 
