#include "axiom"

extend Boolean: BasicType with {
       true: %;
       false: %;
} == add {
  Rep ==> XLisp;
  import from Rep;
  true: % == per(T()$XLisp);
  false: % == per NIL();
  (a: %) = (b: %): Boolean == EQ(rep(a), rep(b));
  (a: %) ~= (b: %): Boolean == not(a=b);
}
