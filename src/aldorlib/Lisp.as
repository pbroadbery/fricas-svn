#include "axiom.as"


XLisp: with {
  EQ: (%, %) -> Boolean
} == add {
  import {
       cons: (%, %) -> %;
       car: % -> %;
       cdr: % -> %;
       nil: %;
       eq: (%, %) -> Boolean;
       null: % -> Boolean;
  } from Foreign Lisp;

  default l, x, y: %;
  lisp(T: with)(t: T): % == t pretend %;

  CONS(x, l): % == CONS(x, l);
  CAR(l): % == car(l);
  CDR(l): % == cdr(l);
  null?(x): Boolean == null(x);
  EQ(x, y): Boolean == EQ(x, y);

}


