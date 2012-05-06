--DEPS:  UnaryRecursiveAggregate LinearAggregate 
#include "axiom.as"

import from Boolean;
import from String;
import from System;

StreamAggregate(S:Type): Category == 
   Join(UnaryRecursiveAggregate S, LinearAggregate S) with {
      explicitlyFinite?: % -> Boolean;
        ++ explicitlyFinite?(s) tests if the stream has a finite
        ++ number of elements, and false otherwise.
        ++ Note: for many datatypes, \axiom{explicitlyFinite?(s) = not possiblyInfinite?(s)}.
      possiblyInfinite?: % -> Boolean;
        ++ possiblyInfinite?(s) tests if the stream s could possibly
        ++ have an infinite number of elements.
        ++ Note: for many datatypes, \axiom{possiblyInfinite?(s) = not explictlyFinite?(s)}.
 default {
   import from List S;
   import from Segment Integer;
   default x, r, l: %;
   default n: Integer;

   explicitlyFinite? x: Boolean == not cyclic? x;
   possiblyInfinite? x: Boolean == cyclic? x;
   first(x, n): % == construct [c2(x, x := rest x) for i in 1..n];

   local c2(x, r): S == {
     empty? x => error "Index out of range";
     first x}

   elt(x:%, i:Integer): S == {
     i := i - minIndex x;
     (i < 0) or empty?(x := rest(x, i::NonNegativeInteger)) => error "index out of range";
     first x}

   elt(x:%, i:UniversalSegment(Integer)): % == {
     low: Integer := lo(i) - minIndex x;
     low < 0 => error "index out of range";
     not hasHi i => copy(rest(x, low::NonNegativeInteger));
     (h := hi(i) - minIndex x) < low => empty();
     first(rest(x, low::NonNegativeInteger), (h - low + 1)::NonNegativeInteger)}

   if % has shallowlyMutable then {
     concat(x:%, y:%): % == concat!(copy x, y);

     concat(ls: List %): % == {
       empty? ls => empty();
       l1 := reverse ls;
       res: % := empty();
       for x in l1 repeat
           res := concat!(copy x, res);
       res}

     map!(f: S->S, l): % == {
       y := l;
       while not empty? l repeat {
         setfirst!(l, f first l);
         l := rest l}
       y}

     fill!(x, s: S): % == {
       y := x;
       while not empty? y repeat (setfirst!(y, s); y := rest y);
       x}

     setelt(x:%, i:Integer, s:S): S == {
      i := i - minIndex x;
      (i < 0) or empty?(x := rest(x,i::NonNegativeInteger)) => error "index out of range";
      setfirst!(x, s)}

     setelt(x:%, i:UniversalSegment(Integer), s:S): S == {
      (li := lo(i) - minIndex x) < 0 => error "index out of range";
      h := if hasHi i then hi(i) - minIndex x else maxIndex x;
      h < li => s;
      y := rest(x, li::NonNegativeInteger);
      z := rest(y, (h - li + 1)::NonNegativeInteger);
      while not eq?(y, z) repeat (setfirst!(y, s); y := rest y);
      s}

     concat!(x:%, y:%): % == {
       empty? x => y;
       setrest!(tail x, y);
       x}
}
}
}