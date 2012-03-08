--DEPS: Segment_SegmentCategory OutputForm String_SetCategory init_UniversalSegment
--DEPS: Integer_SetCategory
#include "axiom.as"

import from Boolean;
import from System;
import from String;

extend UniversalSegment(S: with): SegmentCategory(S) with {
    SEGMENT: S -> %;
        ++ \spad{l..} produces a half open segment,
        ++ that is, one with no upper bound.
    segment: S -> %;
        ++ segment(l) is an alternate way to construct the segment \spad{l..}.
    coerce : Segment S -> %;
        ++ coerce(x) allows \spadtype{Segment} values to be used as %.
    hasHi: % -> Boolean;
        ++ hasHi(s) tests whether the segment s has an upper bound.
	
    ..: S -> %;
    ..: (S, S) -> %;
    
    if S has SetCategory then SetCategory;
    if S has OrderedRing then {
       generator: % -> Generator S;
    }
}  == add {
    Rec  ==> Record(low: S, high: S, incr: Integer);
    Rec2 ==> Record(low: S, incr: Integer);
    SEG ==> Segment S;

    Rep == Union(bounded: Rec, unbounded: Rec2);
    import from Rep, Rec, Rec2;
    default a,b : S;
    default s : %;
    default i: Integer;
    default ls : List %;

    segment a: % == per union([a, 1]);
    segment(a,b): % == per union([a,b,1]);
    BY(s,i): % == {
      rep(s) case unbounded => per union([lo s, hi s, i]);
      per union([lo s, i]);
    }
    lo s: S == {
      rep(s) case bounded => (rep(s).bounded).low;
      rep(s).unbounded.low;
    }
    
    (a: S).. : % == per union [a, 1];
    (a: S)..(b: S) : % == per union [a, b, 1];
    low s: S == lo s;

    hasHi s: Boolean == rep(s) case bounded;

    hi s: S == {
      not hasHi(s) => error "hi: segment has no upper bound";
      rep(s).bounded.high;}

    high s: S == hi s;

    incr s: Integer == {
      rep(s) case bounded => rep(s).bounded.incr;
      rep(s).unbounded.incr;}

    SEGMENT(a): % == segment a;
    SEGMENT(a,b): % == segment(a,b);

    coerce(sg : SEG): % == segment(lo sg, hi sg);

    convert a: % == per union([a,a,1]);

    if S has SetCategory then {

       (seg1:%) = (seg2:%): Boolean == {
          s1 := rep(seg1);
	  s2 := rep(seg2);
          s1 case unbounded => {
             s2 case unbounded =>
                 s1.unbounded.low = s2.unbounded.low and s1.unbounded.incr = s2.unbounded.incr;
             false;}
          s1 case bounded => {
             s2 case bounded =>
                 s2.bounded.low = s2.bounded.low and s1.bounded.high=s2.bounded.high and s1.bounded.incr=s2.bounded.incr;
             false}
          false}

       coerce(s: %): OutputForm == {
         seg := {
           e := (lo s)::OutputForm;
           hasHi s => SEGMENT(e, (hi s)::OutputForm);
           SEGMENT e}
         inc := incr s;
         inc = 1 => seg;
         infix(" by "::OutputForm, seg, inc::OutputForm)}
    }
    if S has OrderedRing then {
       generator(x: %): Generator S == generate {
           t := lo x;
	   while t <= hi x repeat { yield t; t := t + (incr x)::S }
       }
    }
 convert(s: %): InputForm == never;
  
}