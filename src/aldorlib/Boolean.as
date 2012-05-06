--DEPS:  init_Boolean BasicType Basic
#include "axiom"

extend Boolean: BasicType with {
       true: %;
       false: %;
       coerce: BasicBoolean -> %;
       _not: % -> %;
       _and: (%, %) -> %;
       _or: (%, %) -> %;
       \/: (%, %) -> %;
       /\: (%, %) -> %;
       nand: (%, %)-> %;
       nor: (%, %) -> %;
       xor: (%, %) -> %;
} == add {
  Rep ==> BasicBoolean;
  import from Rep;

  coerce(x: BasicBoolean): % == per x;

  true: % == per true();
  false: % == per false();
  (a: %) = (b: %): % == per(equal(rep a, rep b));
  (a: %) ~= (b: %): % == not(a=b);
  (a: %) \/ (b: %): % == a or b;
  (a: %) /\ (b: %): % == a and b;
  nand(a: %, b: %): % == not(a and b);
  nor(a: %, b: %): % == not(a or b);
  xor(a: %, b: %): % == a and not b or b and not a;
  _and(a: %, b: %): % == a and b;
  _or(a: %, b: %): % == a or b;
  _not(a: %): % == not a;
}
