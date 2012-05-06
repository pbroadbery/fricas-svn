--DEPS:  lang init_Boolean 
#include "axiom"

BasicInteger: with {
  one: () -> %;
  zero: () -> %;
  zero?: % -> BasicBoolean;
  positive?: % -> BasicBoolean;
  negative?: % -> BasicBoolean;
  even?: % -> BasicBoolean;
  odd?: % -> BasicBoolean;
  negate: % -> %;
  +: (%, %) -> %;
  -: (%, %) -> %;
  *: (%, %) -> %;
  ^: (%, %) -> %;
  mod: (%, %) -> %;
  quo: (%, %) -> %;
  rem: (%, %) -> %;
  divide: (%, %) -> (%, %);
  =: (%, %) -> BasicBoolean;
  ~=: (%, %) -> BasicBoolean;
  >: (%, %) -> BasicBoolean;
  <: (%, %) -> BasicBoolean;
  >=: (%, %) -> BasicBoolean;
  <=: (%, %) -> BasicBoolean;

  powmod: (%, %, %) -> %;
}
== add {
  import from Boolean;
  import {
        BInt0: () -> %;
	BInt1: () -> %;
	BIntIsZero: (%) -> BasicBoolean;
	BIntIsNeg: (%) -> BasicBoolean;
	BIntIsPos: (%) -> BasicBoolean;
	BIntIsEven: (%) -> BasicBoolean;
	BIntIsOdd: (%) -> BasicBoolean;
	BIntIsSingle: (%) -> BasicBoolean;
	BIntEQ: (%, %) -> BasicBoolean;
	BIntNE: (%, %) -> BasicBoolean;
	BIntLT: (%, %) -> BasicBoolean;
	BIntLE: (%, %) -> BasicBoolean;
	BIntNegate: (%) -> %;
	BIntPrev: (%) -> %;
	BIntNext: (%) -> %;
	BIntPlus: (%, %) -> %;
	BIntMinus: (%, %) -> %;
	BIntTimes: (%, %) -> %;
	BIntTimesPlus: (%,%,%) -> %;
	BIntMod: (%, %) -> %;
	BIntQuo: (%, %) -> %;
	BIntRem: (%, %) -> %;
	BIntDivide: (%, %) -> (%, %);
	BIntGcd: (%, %) -> %;
	BIntSIPower: (%, BasicSingleInteger) -> %;
	BIntBIPower: (%, %) -> %;
	BIntPowerMod: (%, %, %) -> %;
	BIntLength: (%) -> BasicSingleInteger;
	BIntShiftUp: (%, BasicSingleInteger) -> %;
	BIntShiftDn: (%, BasicSingleInteger) -> %;
	BIntShiftRem: (%, BasicSingleInteger) -> %;
	BIntBit: (%, BasicSingleInteger) -> BasicBoolean;
  } from Foreign Builtin;
  default x, y, z: %;

  one(): % == BInt1();
  zero(): % == BInt0();
  zero?(x): BasicBoolean == BIntIsZero x;
  negative? x: BasicBoolean == BIntIsNeg x;
  positive? x: BasicBoolean == BIntIsPos x;
  even? x: BasicBoolean == BIntIsEven x;
  odd? x: BasicBoolean == BIntIsOdd x;
  negate x: % == BIntNegate x;
  (+)(x, y): % == BIntPlus(x, y);
  (-)(x, y): % == BIntMinus(x, y);
  (*)(x, y): % == BIntTimes(x, y);
  (^)(x, y): % == BIntBIPower(x, y);
  (mod)(x, y): % == BIntMod(x, y);
  (quo)(x, y): % == BIntQuo(x, y);
  (rem)(x, y): % == BIntRem(x, y);
  divide(x, y): (%, %) == BIntDivide(x, y);
  (=)(x, y): BasicBoolean == BIntEQ(x, y);
  (~=)(x, y): BasicBoolean == BIntEQ(x, y);
  
  x > y: BasicBoolean ==  BIntLT(y, x);
  x < y: BasicBoolean ==  BIntLT(x, y);
  x >= y: BasicBoolean == BIntLE(y, x);
  x <= y: BasicBoolean == BIntLE(x, y);

  powmod(x, y, z): % == BIntPowerMod(x, y, z);
}

BasicArray: with {
   convert: % -> BasicSFloat;
   convert: % -> BasicDFloat;
   convert: % -> BasicSingleInteger;
   convert: % -> BasicInteger;
   
   coerce: Literal -> %;
}
== add {
   import {
      ArrToSFlo: % -> BasicSFloat;
      ArrToDFlo: % -> BasicDFloat;
      ArrToSInt: % -> BasicSingleInteger;
      ArrToBInt: % -> BasicInteger;
   } from Foreign Builtin;

   convert(a: %): BasicSFloat == ArrToSFlo a;
   convert(a: %): BasicDFloat == ArrToDFlo a;
   convert(a: %): BasicSingleInteger == ArrToSInt a;
   convert(a: %): BasicInteger == ArrToBInt a;

   coerce(l: Literal): % == l pretend %;
}

BasicSFloat: with {

}
== add {

}

BasicDFloat: with {

}
== add {

}

BasicBoolean: with {
   true: () -> %;
   false: () -> %;
   _and: (%, %) -> %;
   _or: (%, %) -> %;
   equal: (%, %) -> %;
   notEqual: (%, %) -> %;
}
== add {
   import {
      BoolTrue: () -> %;
      BoolFalse: () -> %;
      BoolNot: % -> %;
      BoolAnd: (%, %) -> %;
      BoolOr: (%, %) -> %;
      BoolEQ: (%, %) -> %;
      BoolNE: (%, %) -> %;
   } from Foreign Builtin;

   default a, b: %;
   true(): % == BoolTrue();
   false(): % == BoolFalse();
   _and(a, b): % == BoolAnd(a, b);
   _or(a, b): % == BoolOr(a, b);
   equal(a, b): % == BoolEQ(a, b); 
   notEqual(a, b): % == BoolNE(a, b); 
}

BasicSingleInteger: with {

}
== add {

}