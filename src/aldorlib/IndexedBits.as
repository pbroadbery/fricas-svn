--DEPS: BitAggregate Integer
#include "axiom.as"
#pile

import from System
import from String
import from Boolean

IndexedBits(mn:Integer): BitAggregate with
        -- temporaries until parser gets better
        Not: % -> %
            ++ Not(n) returns the bit-by-bit logical {\em Not} of n.
        Or : (%, %) -> %
            ++ Or(n,m)  returns the bit-by-bit logical {\em Or} of
            ++ n and m.
        And: (%, %) -> %
            ++ And(n,m)  returns the bit-by-bit logical {\em And} of
            ++ n and m.
    == add
        default u, v: %
	default i: Integer
	default b: Boolean
	default n: NonNegativeInteger
	import from UniversalSegment Integer
          --++ range(j,i) returnes the range i of the boolean j.
	Rep ==> BitLisp;
	import from Rep;

        minIndex u: Integer  == mn

        local range(v, i): Integer ==
          i >= 0 and i < #v::Integer => i
          error "Index out of range"

        coerce(v): OutputForm ==
            t:Character := char "1"
            f:Character := char "0"
            s := new(#v, space()$Character)$String
            for i in minIndex(s)..maxIndex(s) for j in mn.. repeat
              s.i := if v.j then t else f
            s::OutputForm

        new(n, b): %       == per(LBVEC_-MAKE_-FULL(n,LTRUTH_-TO_-BIT(b)$BitLisp)$BitLisp)
        empty(): %         == per(LBVEC_-MAKE_-FULL(0,0$Integer)$BitLisp)
        copy v: %          == per(LBVEC_-COPY(rep v)$BitLisp)
        #v: NonNegativeInteger == (LBVEC_-SIZE(rep v)$BitLisp)::NonNegativeInteger
        v = u: Boolean     == LBVEC_-EQUAL(rep v, rep u)$BitLisp
        v < u: Boolean     == LBVEC_-GREATER(rep u, rep v)$BitLisp
        _and(u, v): %      == (#v=#u => per(LBVEC_-AND(rep v, rep u)$BitLisp); map(_and,v,u))
        _or(u, v): %       == (#v=#u => per(LBVEC_-OR(rep v, rep u)$BitLisp); map(_or, v,u))
        xor(v,u): %        == (#v=#u => per(LBVEC_-XOR(rep v, rep u)$BitLisp); map(xor,v,u))
        setelt(v:%, i:Integer, f:Boolean): Boolean ==
          LBVEC_-SETELT(rep v, range(v, i-mn), LTRUTH_-TO_-BIT(f)$BitLisp)$BitLisp
        elt(v:%, i:Integer): Boolean ==
          LBIT_-TO_-TRUTH(LBVEC_-ELT(rep v, range(v, i-mn))$BitLisp)$BitLisp

        Not v: %           == per(LBVEC_-NOT(rep v)$BitLisp)
        And(u, v): %       == (#v=#u => per(LBVEC_-AND(rep v, rep u)$BitLisp); map(_and,v,u))
        Or(u, v): %        == (#v=#u => per(LBVEC_-OR(rep v, rep u)$BitLisp); map(_or, v,u))

local BitLisp: with {
      LBVEC_-MAKE_-FULL: (NonNegativeInteger, Integer) -> %;
      LTRUTH_-TO_-BIT: Boolean -> Integer;
      LBIT_-TO_-TRUTH: Integer -> Boolean;
      LBVEC_-NOT: % -> %;
      LBVEC_-COPY: % -> %;
      LBVEC_-SIZE: % -> Integer;
      LBVEC_-EQUAL: (%, %) -> Boolean;
      LBVEC_-GREATER: (%, %) -> Boolean;
      LBVEC_-AND: (%, %) -> %;
      LBVEC_-OR: (%, %) -> %;
      LBVEC_-XOR: (%, %) -> %;
      LBVEC_-NOT: % -> %;
      LBVEC_-ELT: (%, Integer) -> Integer;
      LBVEC_-SETELT: (%, Integer, Integer) -> Boolean;
}
== add {
   import {
      BVEC_-MAKE_-FULL: (NonNegativeInteger, Integer) -> %;
      TRUTH_-TO_-BIT: Boolean -> Integer;
      BIT_-TO_-TRUTH: Integer -> Boolean;
      BVEC_-SIZE: % -> Integer;
      BVEC_-EQUAL: (%, %) -> Boolean;
      BVEC_-GREATER: (%, %) -> Boolean;
      BVEC_-AND: (%, %) -> %;
      BVEC_-OR: (%, %) -> %;
      BVEC_-XOR: (%, %) -> %;
      BVEC_-NOT: % -> %;
      BVEC_-COPY: % -> %;
      BVEC_-ELT: (%, Integer) -> Integer;
      BVEC_-SETELT: (%, Integer, Integer) -> Boolean;
   } from Foreign Lisp;
   default b, c: %;
   
   LBVEC_-MAKE_-FULL(n: NonNegativeInteger, f: Integer): % == BVEC_-MAKE_-FULL(n, f);
   LTRUTH_-TO_-BIT(f: Boolean): Integer == TRUTH_-TO_-BIT(f);
   LBIT_-TO_-TRUTH(n: Integer):  Boolean == BIT_-TO_-TRUTH(n);
   LBVEC_-SIZE b: Integer == BVEC_-SIZE(b);
   LBVEC_-EQUAL(b, c):  Boolean == BVEC_-EQUAL(b, c);
   LBVEC_-GREATER (b, c): Boolean == BVEC_-GREATER(b, c);
   LBVEC_-AND(b, c): % == BVEC_-AND(b, c);
   LBVEC_-OR(b, c): % == BVEC_-OR(b, c);
   LBVEC_-XOR(b, c): % == BVEC_-XOR(b, c);
   LBVEC_-NOT b: % == BVEC_-NOT(b);
   LBVEC_-COPY b: % == BVEC_-COPY(b);
   LBVEC_-ELT(b, n: Integer): Integer == BVEC_-ELT(b, n);
   LBVEC_-SETELT(b, n: Integer, m: Integer): Boolean == BVEC_-SETELT(b, n, m);
}
