#include "axiom.as"

extend XLisp: with {
   EQ: (%, %) -> Boolean;
   T: () -> %;
   NIL: () -> %;
   NULL?: % -> Boolean;
   lisp: (T: with) -> T -> %;
   CONS: (%, %) -> %;
} == add {

  import {
       cons: (%, %) -> %;
       car: % -> %;
       cdr: % -> %;
       nil: %;
       eq: (%, %) -> Boolean;
       null: % -> Boolean;
       t: %;
  } from Foreign Lisp;

  default l, x, y: %;
  lisp(T: with)(t: T): % == t pretend %;

  CONS(x, l): % == CONS(x, l);
  CAR(l): % == car(l);
  CDR(l): % == cdr(l);
  NULL?(x): Boolean == null(x);
  EQ(x, y): Boolean == eq(x, y);
  T(): % == t;
  NIL(): % == nil;
}


