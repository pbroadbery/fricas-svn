--DEPS:  lang init_Boolean init_XLisp init_String init_Pointer
#include "axiom.as"

extend XLisp: with {
   EQ: (%, %) -> Boolean;
   T: () -> %;
   NIL: () -> %;
   NULL: % -> Boolean;
   ATOM: % -> Boolean;
   PAIRP: % -> Boolean;
   STRINGP: % -> Boolean;
--   INTEGERP: % -> Boolean;
--   FLOATP: % -> Boolean;
--   IDENTP: % -> Boolean;
   
   CONS: (%, %) -> %;
   CAR: % -> %;
   CDR: % -> %;
   RPLACA: (%, %) -> ();
   RPLACD: (%, %) -> ();
--   LENGTH: % -> %;
--   EQUAL: (%, %) -> Boolean;
   EQ: (%, %) -> Boolean;
   EQCAR: (%, %) -> Boolean;

--   QVMAXINDEX: % -> %;
--   QVSIZE: % -> %;
--   QAREF1: (%, %) -> %;
--   QSETAREF1: (%, %, %) -> %;
--   MAKE_-ARRAY: % -> %;
--   MAKEARR1: (%, %) -> %;
--   INTERN: % -> %;

--   NUMBERP: % -> Boolean;
--   READ_-FROM_-STRING: % -> %;

--   STRINGIMAGE: % -> %;
--   PARSE_-INTEGER: % -> %;
--   LIST2VEC: % -> %;
--   0: %;

--   lisp: (T: with) -> T -> %;
   lisp: (T: with) -> T -> %;
   unlisp: (T: with) -> % -> T;

--   CHAR_-AT: (%, %) -> %;
} == add {
   import from Machine;

   Rep ==> Union(nil: Pointer, pair: LPair, string: String, other: LDepCross);
   import from Rep;
   import from LPair;
   import from LDepCross;

   EQ(a: %, b: %): Boolean == (rep(a) pretend Ptr$Machine = rep(b) pretend Ptr$Machine) pretend Boolean;
   T(): % == NIL(); --FIXME
   NIL(): % == per [nil$Machine pretend Pointer];
   NULL(p: %): Boolean == rep(p) case nil;
   ATOM(p: %): Boolean == not(rep(p) case pair);
   PAIRP(p: %): Boolean == rep(p) case pair;
   STRINGP(p: %): Boolean == rep(p) case string;
--   INTEGERP(p: %): Boolean == rep(p) case integer;
--   FLOATP(p: %): Boolean == rep(p) case float;
--   IDENTP(p: %): Boolean == rep(p) case symbol;
   
   CAR(p: %): % == car(rep(p).pair);
   CDR(p: %): % == car(rep(p).pair);
   CONS(p: %, q: %): % == per [cons(p, q)];
   RPLACA(p: %, v: %): () == setcar!(rep(p).pair, v);
   RPLACD(p: %, v: %): () == setcdr!(rep(p).pair, v);

   EQUAL(p: %, q: %): Boolean == never;
   EQCAR(p: %, q: %): Boolean == EQ(CAR(p), q);

   X == Cross(T: with, T);
   lisp(T: with)(t: T): % == {
   	   import from LDepCross;
   	   T has TheString => per [t pretend String];
	   per [new(T, t pretend T)];
   }
   unlisp(T: with)(a: %): T == {
   	     rep(a) case string => {
	     	    T has TheString => never;
		    rep(a).string pretend T;
             }
	     depcross := rep(a).other;	     
	     (Q, q) == value depcross;
	     q pretend T;
   }
   
}

LDepCross: with {
   new: (A: with, A) -> %;
   value: % -> (T: with, T);
} 
== add {
   Rep ==> Cross(T: with, T);
   import from Rep;

   new(A: with, a: A): % == { c := (A, a); c pretend %; }
   value(a: %): (T: with, t: T) == rep a;
}

LPair: with {
      cons: (XLisp, XLisp) -> %;
      car: % -> XLisp;
      cdr: % -> XLisp;
      setcar!: (%, XLisp) -> ();
      setcdr!: (%, XLisp) -> ();
} 
== add {
  Rep ==> Record(car: XLisp, cdr: XLisp);
  import from Rep;
  default p: %;
  cons(a: XLisp, b: XLisp): % == per [a, b];

  car(p: %): XLisp == rep(p).car;
  cdr(p: %): XLisp == rep(p).cdr;
  
  setcar!(p: %, v: XLisp): () == rep(p).car := v;
  setcdr!(p: %, v: XLisp): () == rep(p).cdr := v;

}