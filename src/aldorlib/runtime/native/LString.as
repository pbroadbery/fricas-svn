--DEPS:  SingleInteger init_Character init_Integer Boolean
#include "axiom.as"

LString: with {
    QENUM: (%, SingleInteger) -> Character;
    QESET: (%, SingleInteger, Character) -> ();
    NEW: SingleInteger -> %;
    bytes: % -> Bytes;
    string: Literal -> %;
    string: Integer -> %;
    string: SingleInteger -> %;
    length: % -> SingleInteger;

    =: (%, %) -> Boolean;
} 
== add {
    import from Machine;
    Rep ==> Record(sz: SingleInteger, arr: CharArray);
    import from Rep;

    length(a: %): SingleInteger == rep(a).sz;
    QENUM(a: %, n: SingleInteger): Character == { CHK(a, n); rep(a).arr.n;}
    QESET(a: %, n: SingleInteger, c: Character): () == {CHK(a, n); rep(a).arr.n := c;}

    NEW(n: SingleInteger): % == per [n, new(n)];

    string(l: Literal): % == string(l pretend CharArray);
    string(n: Integer): % == string(charArray n);
    string(n: SingleInteger): % == string(charArray n);

    string(arr: CharArray): % == per [length arr, arr];
    bytes(a: %): Bytes == rep(a).arr pretend Bytes;

    (a: %) = (b: %): Boolean == {
       length a ~= length b => false;
       i: SingleInteger := 0;
       while i < length a repeat {
       	     if rep(a).arr.i ~= rep(b).arr.i then return false;
	     i := i + 1;
       }
       return true;
    }

    local CHK(a: %, n: SingleInteger): () == {
    	  if n >= length a then never;
    }

    local (a: Character) ~= (b: Character): Boolean == ((a pretend Char) ~= (b pretend Char)) pretend Boolean;
}

Bytes: with == add;

local CharArray: with {
      new: (SingleInteger, Character) -> %;
      new: (SingleInteger) -> %;
      apply: (%, SingleInteger) -> Character;
      set!: (%, SingleInteger, Character) -> ();
      charArray: Integer -> %;
      charArray: SingleInteger -> %;
      length: % -> SingleInteger;
}
== add {
   import from Machine;
   Rep ==> Arr;
   local sint(x: SingleInteger): SInt == x pretend SInt;

   import {
                ArrNew: (Char, SInt) -> Arr;
                ArrElt: (Arr,  SInt) -> Char;
                ArrSet: (Arr,  SInt, Char) -> Char;
   } from Builtin;

   import { formatBInt: BInt -> Arr } from Foreign;
   import { formatSInt: SInt -> Arr } from Foreign;
   import { strLength: Arr -> SInt } from Foreign;
   new(n: SingleInteger, c: Character): % == {
   	  --c == 0 => never;-- FIXME, needed.
   	  a := per ArrNew(c pretend Char, n pretend SInt);
	  i: SingleInteger := 0;
	  while i < n repeat { a.i := c; i := i+1}
	  a
   }

   new(n: SingleInteger): % == {
   	  per ArrNew(newline, n pretend SInt);
    }

   apply(s: %, n: SingleInteger): Character == ArrElt(rep s, n pretend SInt) pretend Character;
   set!(s: %, n: SingleInteger, c: Character): () == ArrSet(rep s, n pretend SInt, c pretend Char);

   import { formatBInt: BInt -> Arr } from Foreign;
   import { formatSInt: SInt -> Arr } from Foreign;
   import { strLength: Arr -> SInt } from Foreign;

   charArray(x: SingleInteger): % == per formatSInt(x pretend SInt);
   charArray(x: Integer): % == per formatBInt(x pretend BInt);
   length(s: %): SingleInteger == strLength(rep s) pretend SingleInteger;
}
