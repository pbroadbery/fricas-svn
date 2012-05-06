--DEPS: SegmentCategory SetCategory SegmentExpansionCategory
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
    if S has SetCategory then {
      coerce(s:%):OutputForm == {
        seg := SEGMENT(s.low::OutputForm, s.high::OutputForm);
        s.incr = 1 => seg;
        infix(" by "::OutputForm, seg, s.incr::OutputForm)}

       (a: %) = (b: %): Boolean == low a = low b and high a = high b;
    }
    if S has OrderedRing then {
      expand(ls: List %):List S == {
        lr := nil()$List(S);
        for s in ls repeat {
          l := lo s;
          h := hi s;
          inc := (incr s)::S;
          zero? inc => error "Cannot expand a segment with an increment of zero";
          if inc > 0 then {
            while l <= h repeat {
              lr := concat(l, lr);
              l := l + inc}
          }
	  else {
            while l >= h repeat {
              lr := concat(l, lr);
              l := l + inc;
            }}
        }
        reverse! lr}

      expand(s : %): List S == [e for e in s];
      map(f : S->S, s : %): List S == {
        lr := nil()$List(S);
        l := lo s;
        h := hi s;
        inc := (incr s)::S;
        if inc > 0 then {
          while l <= h repeat {
            lr := concat(f l, lr);
            l := l + inc}}
        else {
          while l >= h repeat {
            lr := concat(f l, lr);
            l := l + inc;}}
        reverse! lr
	}
   }
}
