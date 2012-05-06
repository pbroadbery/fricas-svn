--DEPS: RecursiveAggregate System Segment_SegmentCategory UniversalSegment 
--DEPS: Integer_OrderedRing NonNegativeInteger_SemiRing OrderedSemiRingSegment
#include "axiom.as"

import from Boolean;
import from System;
import from String;
import from Integer;

UnaryRecursiveAggregate(S:Type): Category == RecursiveAggregate S with {
   concat: (%,%) -> %;
      ++ concat(u,v) returns an aggregate w consisting of the elements of u
      ++ followed by the elements of v.
      ++ Note: \axiom{v = rest(w,#a)}.
   concat: (S,%) -> %;
      ++ concat(x,u) returns aggregate consisting of x followed by
      ++ the elements of u.
      ++ Note: if \axiom{v = concat(x,u)} then \axiom{x = first v}
      ++ and \axiom{u = rest v}.
   first: % -> S;
      ++ first(u) returns the first element of u
      ++ (equivalently, the value at the current node).
   elt: (%,'first') -> S;
      ++ elt(u,'first') (also written: \axiom{u . first}) is equivalent to first u.
   first: (%,NonNegativeInteger) -> %;
      ++ first(u,n) returns a copy of the first n (\axiom{n >= 0}) elements of u.
   rest: % -> %;
      ++ rest(u) returns an aggregate consisting of all but the first
      ++ element of u
      ++ (equivalently, the next node of u).
   elt: (%,'rest') -> %;
      ++ elt(%,"rest") (also written: \axiom{u.rest}) is
      ++ equivalent to \axiom{rest u}.
   rest: (%,NonNegativeInteger) -> %;
      ++ rest(u,n) returns the \axiom{n}th (n >= 0) node of u.
      ++ Note: \axiom{rest(u,0) = u}.
   last: % -> S;
      ++ last(u) resturn the last element of u.
      ++ Note: for lists, \axiom{last(u) = u . (maxIndex u) = u . (# u - 1)}.
   elt: (%,'last') -> S;
      ++ elt(u,"last") (also written: \axiom{u . last}) is equivalent to last u.
   last: (%,NonNegativeInteger) -> %;
      ++ last(u,n) returns a copy of the last n (\axiom{n >= 0}) nodes of u.
      ++ Note: \axiom{last(u,n)} is a list of n elements.
   tail: % -> %;
      ++ tail(u) returns the last node of u.
      ++ Note: if u is \axiom{shallowlyMutable},
      ++ \axiom{setrest(tail(u),v) = concat(u,v)}.
   second: % -> S;
      ++ second(u) returns the second element of u.
      ++ Note: \axiom{second(u) = first(rest(u))}.
   third: % -> S;
      ++ third(u) returns the third element of u.
      ++ Note: \axiom{third(u) = first(rest(rest(u)))}.
   cycleEntry: % -> %;
      ++ cycleEntry(u) returns the head of a top-level cycle contained in
      ++ aggregate u, or \axiom{empty()} if none exists.
   cycleLength: % -> NonNegativeInteger;
      ++ cycleLength(u) returns the length of a top-level cycle
      ++ contained  in aggregate u, or 0 is u has no such cycle.
   cycleTail: % -> %;
      ++ cycleTail(u) returns the last node in the cycle, or
      ++ empty if none exists.
   if % has shallowlyMutable then {
      concat!: (%,%) -> %;
        ++ concat!(u,v) destructively concatenates v to the end of u.
        ++ Note: \axiom{concat!(u,v) = setlast!(u,v)}.
      concat!: (%,S) -> %;
        ++ concat!(u,x) destructively adds element x to the end of u.
        ++ Note: \axiom{concat!(a,x) = setlast!(a,[x])}.
      cycleSplit!: % -> %;
        ++ cycleSplit!(u) splits the aggregate by dropping off the cycle.
        ++ The value returned is the cycle entry, or nil if none exists.
        ++ For example, if \axiom{w = concat(u,v)} is the cyclic list where v is
        ++ the head of the cycle, \axiom{cycleSplit!(w)} will drop v off w thus
        ++ destructively changing w to u, and returning v.
      setfirst!: (%,S) -> S;
        ++ setfirst!(u,x) destructively changes the first element of a to x.
      setelt: (%,'first',S) -> S;
        ++ setelt(u,'first',x) (also written: \axiom{u.first := x}) is
        ++ equivalent to \axiom{setfirst!(u,x)}.
      setrest!: (%,%) -> %;
        ++ setrest!(u,v) destructively changes the rest of u to v.
      setelt: (%,'rest',%) -> %;
        ++ setelt(u,'rest',v) (also written: \axiom{u.rest := v}) is equivalent to
        ++ \axiom{setrest!(u,v)}.
      setlast!: (%,S) -> S;
        ++ setlast!(u,x) destructively changes the last element of u to x.
      setelt: (%,'last',S) -> S;
        ++ setelt(u,'last',x) (also written: \axiom{u.last := b})
        ++ is equivalent to \axiom{setlast!(u,v)}.
      split!: (%,Integer) -> %;
         ++ split!(u,n) splits u into two aggregates: \axiom{v = rest(u,n)}
         ++ and \axiom{w = first(u,n)}, returning \axiom{v}.
         ++ Note: afterwards \axiom{rest(u,n)} returns \axiom{empty()}.
   }
 default {
  import from UniversalSegment Integer;
  cycleMax ==> 1000;
  import from List %;
  default x, y, u, v, p, q: %;
  default lv: List %;
  default n: NonNegativeInteger;
  default s, a: S;

  elt(x, zzz: 'first'): S == first x;
  elt(x, zzz: 'last'): S  == last x;
  elt(x, zzz: 'rest'): %  == rest x;
  second x: S        == first rest x;
  third x: S         == first rest rest x;
  cyclic? x: Boolean == not empty? x and not empty? findCycle x;
  last x: S          == first tail x;

  nodes x: List % == {
    local l: List %;
    l := empty()$List(%);
    while not empty? x repeat {
      l := concat(x, l);
      x := rest x;
    }
    reverse! l}

  children x: List % == {
    l := empty()$List(%);
    empty? x => l;
    concat(rest x,l)}

  leaf? x: Boolean == empty? x;

  value x: S == {
    empty? x => error "value of empty object";
    first x}

  less?(l: %, n): Boolean == {
    i := n::Integer;
    while i > 0 and not empty? l repeat (l := rest l; i := i - 1);
    i > 0}

  more?(l: %, n): Boolean == {
    i := n::Integer;
    while i > 0 and not empty? l repeat (l := rest l; i := i - 1);
    zero?(i) and not empty? l}

  size?(l: %, n): Boolean == {
    i := n::Integer;
    while not empty? l and i > 0 repeat (l := rest l; i := i - 1);
    empty? l and zero? i}

  #x: NonNegativeInteger == {
    c: NonNegativeInteger := 0;
    for k in 0.. while not empty? x repeat {
      k = cycleMax and cyclic? x => error "cyclic list";
      x := rest x;
      c := c+1;
    }
    c}

  tail x: % == {
    empty? x => error "empty list";
    y := rest x;
    for k in 0.. while not empty? y repeat {
      k = cycleMax and cyclic? x => error "cyclic list";
      y := rest(x := y);
    }
    x}

  findCycle(x): % == {
    y := rest x;
    while not empty? y repeat {
      if eq?(x, y) then return x;
      x := rest x;
      y := rest y;
      if empty? y then return y;
      if eq?(x, y) then return y;
      y := rest y;
    }
    y}

  cycleTail x: % == {
    empty?(y := x := cycleEntry x) => x;
    z := rest x;
    while not eq?(x,z) repeat (y := z; z := rest z);
    y}

  cycleEntry x: % == {
    empty? x => x;
    empty?(y := findCycle x) => y;
    z := rest y;
    l: Integer  := 0;
    for free l in 1.. while not eq?(y,z) repeat z := rest z;
    y := x;
    for k in 1..l repeat y := rest y;
    while not eq?(x,y) repeat (x := rest x; y := rest y);
    x}

  cycleLength x: NonNegativeInteger == {
    import from OrderedSemiRingSegment NonNegativeInteger;
    empty? x => 0;
    empty?(x := findCycle x) => 0;
    y := rest x;
    k: NonNegativeInteger := 0;
    for free k in 1.. while not eq?(x,y) repeat y := rest y;
    k}

  rest(x, n): % == {
    for i in 1..n::Integer repeat {
      empty? x => error "Index out of range";
      x := rest x
    }
    x}

  if % has finiteAggregate then {
    last(x, n): % == {
      n > (m := #x) => error "index out of range";
      copy rest(x, (m - n)::NonNegativeInteger)}
  }

  if S has SetCategory then {
    x = y: Boolean == {
      eq?(x, y) => true;
      for k in 0.. while not empty? x and not empty? y repeat {
        k = cycleMax and cyclic? x => error "cyclic list";
        first x ~= first y => return false;
        x := rest x;
        y := rest y;
      }
      empty? x and empty? y;}

    node?(u, v): Boolean == {
      for k in 0.. while not empty? v repeat {
        u = v => return true;
        k = cycleMax and cyclic? v => error "cyclic list";
        v := rest v;
      }
      u=v}
  }

  if % has shallowlyMutable then {
    default u: %;
    setelt(x, zzz: 'first', a): S == setfirst!(x, a);
    setelt(x, zzz: 'last', a): S == setlast!(x, a);
    setelt(x, zzz: 'rest', cell: %): % == setrest!(x, cell);

    concat(x:%, y:%): % == concat!(copy x, y);

    setlast!(x, s): S == {
      empty? x => error "setlast: empty list";
      setfirst!(tail x, s);
      s}

    setchildren!(u,lv): % == {
      #lv=1 => setrest!(u, first lv);
      error "wrong number of children specified"}

    setvalue!(u,s): S == setfirst!(u,s);

    split!(p, n): % == {
      n < 1 => error "index out of range";
      p := rest(p, (n - 1)::NonNegativeInteger);
      q := rest p;
      setrest!(p, empty());
      q}

    cycleSplit! x: % == {
      empty?(y := cycleEntry x) or eq?(x, y) => y;
      z := rest x;
      while not eq?(z, y) repeat (x := z; z := rest z);
      setrest!(x, empty());
      y}
  }
}
}
