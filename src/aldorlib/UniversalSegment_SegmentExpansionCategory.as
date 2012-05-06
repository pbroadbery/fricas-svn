--DEPS:  init_UniversalSegment SegmentCategory SetCategory SegmentExpansionCategory 
#include "axiom.as"

import from Boolean;

extend UniversalSegment(S: Type): with {
    if S has OrderedRing then {
      SegmentExpansionCategory(S, Stream S);
   }
}  == add {

    if S has OrderedRing then {
      expand(s:%): List S == expand([s]);
      map(f:S->S, s:%): List S  == map(f, expand s);

      plusInc(t: S, a: S): S == t + a;

      expand(ls: List %):Stream S == {
        st:Stream S := empty();
        null ls => st;

        lb:List(Segment S) := nil();
        while not null ls and hasHi first ls repeat {
            s  := first ls;
            ls := rest ls;
            ns := BY(SEGMENT(lo s, hi s), incr s)$Segment(S);
            lb := concat!(lb,ns);}
        if not null ls then {
            s := first ls;
            st: Stream S := generate((x: S): S +-> x + incr(s)::S, lo s)}
        else {
            st: Stream S := empty();}
        concat(construct expand(lb),  st);}
     }

}