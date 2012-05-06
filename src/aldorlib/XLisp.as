--DEPS:  lang init_Boolean init_XLisp 
#include "axiom.as"

extend XLisp: with {
   EQ: (%, %) -> Boolean;
   T: () -> %;
   NIL: () -> %;
   NULL: % -> Boolean;
   ATOM: % -> Boolean;
   PAIRP: % -> Boolean;
   STRINGP: % -> Boolean;
   INTEGERP: % -> Boolean;
   FLOATP: % -> Boolean;
   IDENTP: % -> Boolean;
   
   CAR: % -> %;
   CDR: % -> %;
   RPLACA: (%, %) -> ();
   RPLACD: (%, %) -> ();
   LENGTH: % -> %;
   CONS: (%, %) -> %;
   EQUAL: (%, %) -> Boolean;
   EQ: (%, %) -> Boolean;
   EQCAR: (%, %) -> Boolean;

   QVMAXINDEX: % -> %;
   QVSIZE: % -> %;
   QAREF1: (%, %) -> %;
   QSETAREF1: (%, %, %) -> %;
   MAKE_-ARRAY: % -> %;
   MAKEARR1: (%, %) -> %;
   INTERN: % -> %;

   NUMBERP: % -> Boolean;
   READ_-FROM_-STRING: % -> %;

   STRINGIMAGE: % -> %;
   PARSE_-INTEGER: % -> %;
   LIST2VEC: % -> %;
   0: %;
   lisp: (T: with) -> T -> %;
   unlisp: (T: with) -> % -> T;

   CHAR_-AT: (%, %) -> %;
} == add {
  local LL: with == add;

  import {
       cons: (LL, LL) -> LL;
       car: LL -> LL;
       cdr: LL -> LL;
       rplaca: (LL, LL) -> LL;
       rplacd: (LL, LL) -> LL;
       length: LL -> LL;
       nil: LL;
       eq: (LL, LL) -> Boolean;
       eqcar: (LL, LL) -> Boolean;
       null: LL -> Boolean;
       t: LL;
       zero: () -> LL;
       equal: (LL, LL) -> Boolean;
       eq: (LL, LL) -> Boolean;
       atom: LL -> Boolean;
       pairp: LL -> Boolean;
       stringp: LL -> Boolean;
       identp: LL -> Boolean;
       integerp: LL -> Boolean;
       floatp: LL -> Boolean;
       char_-at: (LL, LL) -> LL;
       numberp: LL -> Boolean;
       read_-from_-string: LL -> LL;
  } from Foreign Lisp;

  default l, x, y: %;
  Rep ==> LL;
  lisp(T: with)(t: T): % == t pretend %;
  unlisp(T: with)(l: %): T == l pretend T;

  CONS(x, l): % == per cons(rep x, rep l);
  CAR(l): % == per car(rep l);
  CDR(l): % == per cdr(rep l);
  RPLACA(l, x): () == rplaca(rep l, rep x);
  RPLACD(l, x): () == rplacd(rep l, rep x);
  LENGTH(l): % == per length(rep l);

  NULL(x): Boolean == null(rep x);
  ATOM(x): Boolean == atom(rep x);
  PAIRP(x): Boolean == pairp(rep x);
  STRINGP(x): Boolean == stringp(rep x);
  IDENTP(x): Boolean == identp(rep x);
  INTEGERP(x): Boolean == integerp(rep x);
  FLOATP(x): Boolean == floatp(rep x);

  EQUAL(x, y): Boolean == eq(rep x, rep y);
  EQ(x, y): Boolean == eq(rep x, rep y);
  EQCAR(x, y): Boolean == eqcar(rep x, rep y);
  T(): % == per t;
  NIL(): % == per nil;

  0: % == per zero();

  QVMAXINDEX(a: %): % == never;
  QVSIZE(a: %): % == never;
  QAREF1(a: %, n: %): % == never;
  QSETAREF1(a: %, n: %, v:%): % == never;
  MAKE_-ARRAY(a: %): % == never;
  MAKEARR1(a: %, v: %): % == never;

  CHAR_-AT(a: %, v: %): % == per char_-at(rep a, rep v);

  NUMBERP(x: %): Boolean == numberp(rep x);
  READ_-FROM_-STRING(x: %): % == per read_-from_-string(rep x);

  STRINGIMAGE(a: %): % == never;
  PARSE_-INTEGER(a: %): % == never;
  LIST2VEC(a: %): % == never;
  INTERN(a: %): % == never;
}


