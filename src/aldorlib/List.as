--DEPS:  init_List XLisp init_Generator NonNegativeInteger SetCategory
#include "axiom.as"

import from Boolean;
import from System;
import from String;

extend List(T: Type): BasicType with {
  nil: () -> %;
  empty: () -> %;
  empty?: % -> Boolean;
  null: % -> Boolean;
  first: % -> T;
  second: % -> T;
  rest: % -> %;
  member?: (T, %) -> Boolean;
  reverse: % -> %;
  cons: (T, %) -> %;
  bracket: Tuple T -> %;
  bracket: Generator T -> %;
  generator: % -> Generator T;
  #: % -> NonNegativeInteger;
  concat: (T, %) -> %;
  concat: (%, %) -> %;
  concat!: (%, %) -> %;
  reverse!: % -> %;
  last: % -> T;
  copy: % -> %;
  split!: (%, Integer) -> %;

  append: (%, %) -> %;

  if T has SetCategory then {
     reduce: ((T, T) -> T, %, T, T) -> T;
     removeDuplicates: % -> %;
     setUnion: (%, %) -> %;
  }

  find: (T -> Boolean, %) -> Partial T;
  reduce: ((T,T) -> T, %) -> T;
  map: (T -> T, %) -> %;
  reduce: ((T,T) -> T, %, T) -> T;
  remove: (T -> Boolean, %) -> %;
  _select: (T -> Boolean, %) -> %;

  apply: (%, 'first') -> T;
  apply: (%, 'rest') -> %;

  set!: (%, 'first', T) -> ();
  set!: (%, 'rest', %) -> ();

  sort: ((T, T) -> Boolean, %) -> %;

  export from 'first', 'rest'
}
 == add {
  Rep ==> XLisp;
  import from Rep;
  import from 'first', 'rest';

  nil(): % == per NIL();
  empty(): % == per NIL();
  empty?(x: %): Boolean == NULL(rep(x));
  null(x: %): Boolean == NULL(rep(x));

  first(x: %): T == unlisp(T)(CAR(rep x));
  rest(x: %): % == per(CDR(rep x));
  
  apply(x: %, zzz: 'first'): T == first(x);
  apply(x: %, zzz: 'rest'): % == rest(x);

  set!(x: %, zzz: 'first', v: T): () == RPLACA(rep x, lisp(T)(v));
  set!(x: %, zzz: 'rest',  r: %): () == RPLACD(rep x, rep (r));
  
  second(x: %): T == first rest x;

  member?(x: T, l: %): Boolean == never;
  (a: %) = (b: %): Boolean == EQ(rep a, rep b);

  [t: Tuple T]: % == never;

  [g: Generator T]: % == {
     l := nil();
     last := nil();
     for elt in g repeat {
        if empty? l then {
	   l := cons(elt, nil());
	   last := l;
	}
	else {
	   last.rest := cons(elt, nil());
	   last := last.rest;
	}
     }
     last;
  }

  cons(e: T, l: %): % == per CONS(lisp(T)(e), rep l);
  generator(l: %): Generator T == generate {
      while not empty? l repeat {
          yield first l;
	  l := rest l;
      }
  }
  #(x: %): NonNegativeInteger == never;
  concat(t: T, l2: %): % == never;
  reverse!(x: %): % == never;
  last(x: %): T == never;
  copy(x: %): % == never;
  split!(x: %, n: Integer): % == never;

  append(t: %, l2: %): % == never;

  find(f: T -> Boolean, l: %): Partial T == never;

  map(f: T->T, x:%): % == [f t for t in x];

  reduce(f:(T,T)->T, x:%): T == {
      empty? x => error "Need at least one..";
      reduce(f, rest x, first x);
  }

  reduce(f:(T,T)->T, x:%, s:T): T == {
      total := s;
      while not empty? x repeat { total := f(total, first x); x := rest x}
      total
  }
  remove(f:T->Boolean, x:%): % == never;
  reverse(x:%): % == never;
  _select(f:T->Boolean, x:%): % == never;

  concat(l1: %, l2: %): % == never;
  concat!(l1: %, l2: %): % == never;

  sort(f: (T, T) -> Boolean, l: %): % == never;

  if T has SetCategory then {
    removeDuplicates(x: %): % == never;
    reduce(f: (T, T) -> T, l: %, init: T, absorb: T): T == {
     acc := init;
     for item in l repeat {
        item = absorb => return absorb;
	acc := f(acc, item);
     }
     acc}
    setUnion(l1: %, l2: %): % == never
}
}

