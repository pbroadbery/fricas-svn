#include "axiom.as"


XLisp: with {
  EQ: (%, %) -> Boolean
} == add {
  import {
       cons: (LL, LL) -> LL;
       car: LL -> LL;
       cdr: LL -> LL;
       nil: LL;
       eq: (LL, LL) -> Boolean;
       null: LL -> Boolean;
  } from Foreign Lisp;
  Rep==>LL

  default l, x, y: %;

  CONS(x, l): % == CONS(rep x, repl);
  CAR(l): % == per car(rep l);
  CDR(l): % == per cdr(rep l);
  null?(x): Boolean == null(rep x);
  EQ(x, y): Boolean == eq(rep x, rep y);

}


