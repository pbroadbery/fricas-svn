--DEPS: SingleInteger init_Character init_Integer runtime/lisp/LString 
--DEPS: init_Boolean init_String
#include "axiom.as"

local LArray(T: Type): with {
	new: (LSInteger, T) -> %;
	get: (%, LSInteger) -> T;
	set: (%, LSInteger, T) -> ();
	#: % -> LSInteger;
} == add {
  Rep ==> Record(size: LSInteger, content: Arr);
  import from Machine;
  import from Rep;
  import from IO;
  import from LString;

  #(a: %): LSInteger == rep(a).size;
  local checkIndex(a: %, index: LSInteger): () == {
  	size := #a;
	if index < 0 or index >= size then { print "Index out of bounds"; never}
  }
  local sint(s: LSInteger): SInt == s pretend SInt;

  new(n: LSInteger, xl: T): % == {
	  a := per [n, array(T)(xl, sint n)];
	  i: LSInteger := 0;
	  while i < n repeat { 
		  set(a, i, xl);
		  i := i+1;
          }
          a
  }
  
  
  local ptrEq(a: T, b: T): Boolean == ((a pretend Ptr) = (b pretend Ptr)) pretend Boolean;
  
  get(a: %, n: LSInteger): T == { 
  	 checkIndex(a, n);
  	 get(T)(rep(a).content, sint n);
  }

  set(a: %, n: LSInteger, xl: T): () == {
  	 checkIndex(a, n);
  	 set!(T)(rep(a).content, sint n, xl);
  }
}

local LSInteger: with {
   0: %;
   1: %;

   integer: Literal -> %;
   coerce: % -> SInt$Machine;
   coerce: % -> Integer;
   coerce: Integer -> %;

   <: (%, %) -> Boolean;
   >: (%, %) -> Boolean;
   >=: (%, %) -> Boolean;
   <=: (%, %) -> Boolean;
   -: (%, %) -> %;
   +: (%, %) -> %;
}
== add {
  import from Machine;
  Rep ==> SInt$Machine;
  0: % == per 0;
  1: % == per 1;
  
  integer(l: Literal): % == per convert(l pretend Arr);
  coerce(n: %): SInt$Machine == rep n;
  coerce(n: %): Integer == (convert rep n)@BInt pretend Integer;
  coerce(n: Integer): % == per convert(n pretend BInt);
  
  (<)(a: %, b: %): Boolean == (rep a < rep b) pretend Boolean;
  (>)(a: %, b: %): Boolean == b < a;
  (<=)(a: %, b: %): Boolean == (rep a <= rep b) pretend Boolean;
  (>=)(a: %, b: %): Boolean == b <= a;

  (-)(a: %, b: %): % == per(rep a - rep b);
  (+)(a: %, b: %): % == per(rep a + rep b);
}

local LCharacter: with {
   newline: () -> %;
} 
== add {
   import from Machine;
   Rep ==> Char;
   newline(): % == per(newline$Machine);
}

IO: with {
   print: LString    -> ();
   print: LCharacter -> ();
   print: SingleInteger -> ();
} 
== add {
   local P: with == add;
   import {
       fputss: (LString, SingleInteger, SingleInteger, P) -> ();
       fputc: (LCharacter, P) -> ();
       stdoutFile: () -> P;
   } from Foreign C;
   import from LSInteger;
   import from LString;

   print(s: LString): () == fputss(s, 0 pretend SingleInteger, length s, stdoutFile());
   print(c: LCharacter): () == fputc(c, stdoutFile());
   print(n: SingleInteger): () == print string(n)
}

ListLisp(T: Type): with {
   CONS: (T, %) -> %;
   CAR: % -> T;
   CDR: % -> %;
   NIL: () -> %;
   NULL: % -> Boolean;
   
   RPLACA: (%, T) -> ();
   RPLACD: (%, %) -> ();
}
== add {
   import from Machine;
   Rep ==> Ptr$Machine;
   local trep(t: T): Rep == t pretend Rep;
   local tper(r: Rep): T == r pretend T;

   import {
      CONS: (Rep, Rep) -> Rep;
      CAR: Rep -> Rep;
      CDR: Rep -> Rep;
      NULL: Rep -> Boolean;

      RPLACA: (Rep, Rep) -> ();
      RPLACD: (Rep, Rep) -> ();
   } from Foreign Lisp;

   CONS(t: T, b: %): % == per CONS(trep t, rep b);
   CAR(a: %): T == tper CAR(rep a);
   CDR(a: %): % == per CDR(rep a);
   NIL(): % == per nil;
   NULL(a: %): Boolean == NULL rep a;

   RPLACA(a: %, t: T): () == RPLACA(rep a, trep t);
   RPLACD(a: %, b: %): () == RPLACD(rep a, rep b);
}

ArrayLisp(T: Type): with {
   QVMAXINDEX: % -> Integer;
   QVSIZE: % -> Integer;
   QAREF1: (%, Integer) -> T;
   QSETAREF1: (%, Integer, T) -> ();
   MAKE_-ARRAY: Integer -> %;
   MAKEARR1: (Integer, T) -> %;
}
== add {
   Rep ==> LArray T;
   default a: %;
   default i: Integer;
   default t: T;
   import from Rep;
   import from LSInteger;
   
   QVMAXINDEX(a): Integer == (#(rep(a)) - 1)::Integer;
   QVSIZE(a): Integer == (#(rep a))::Integer;
   QAREF1(a, i): T == get(rep a, i::LSInteger);
   QSETAREF1(a, i, t): () == set(rep a, i::LSInteger, t);
   
   MAKE_-ARRAY(i): % == never;--per new(i::LSInteger, nil$Machine pretend T);
   MAKEARR1(i, t): % == per new(i::LSInteger, t);
}



