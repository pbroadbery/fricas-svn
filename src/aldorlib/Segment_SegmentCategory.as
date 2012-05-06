--DEPS:  SegmentCategory SetCategory OrderedRing init_Segment
#include "axiom.as"

import from Boolean;

extend Segment(S:Type): SegmentCategory(S) with {
  ..: (S,S) -> %;
    if S has OrderedRing then {
       generator: % -> Generator S;
    }
}
== add {
   default a, b: S;
    default s: %;
    default r: Integer;
    Rep ==> Record(low: S, high: S, incr: Integer);
    import from Rep;

    SEGMENT(a, b): % == a..b;
    a..b: % == per [a,b,1];
    lo s: S == rep(s).low;
    low s: S == rep(s).low;
    hi s: S == rep(s).high;
    high s: S == rep(s).high;
    incr s: Integer == rep(s).incr;
    segment(a,b): % == per [a,b,1];
    BY(s, r): % == per [lo s, hi s, r];

    if S has SetCategory then {
      (s1:%) = (s2:%): Boolean ==
        rep(s1).low = rep(s2).low and rep(s1).high=rep(s2).high and rep(s1).incr = rep(s2).incr;
    }

    convert(a: S): % == per [a,a,1];

    if S has ConvertibleTo InputForm then {
        INFORM1 ==> InputFormFunctions1(%);

        convert(s: %): InputForm == {
	      never;
--            seg := packageCall('SEGMENT,
--                               [convert(low s)@InputForm,
--                                convert(hi s)@InputForm])$INFORM1;
--            if one?(incr s)
--            then seg
--            else packageCall('BY,
--                             [seg, convert(incr s)@InputForm])$INFORM1;
	}
    }

    if S has OrderedRing then {
       generator(x: %): Generator S == 
          if incr x > 0 then generateUp(x);
	  else generateDown(x);
	  
   local generateUp(x: %): Generator S ==  generate {
          lo := low x;
	  hi := high x;
	  inc := incr x;
	  while lo <= hi repeat {
	      yield lo;
	      lo:= lo+inc::S;
	  }
       }
    
   local generateDown(x: %): Generator S == generate {
          a := low x;
	  b := high x;
	  inc := incr x;
	  while a >= b repeat {
	      yield a;
	      a:= a+inc::S;
	  }
       }
    }
    
}
