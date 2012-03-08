--DEPS:  init_String init_Character init_List Integer runtime/c/Local SingleInteger NonNegativeInteger
#include "axiom"

extend String: with {
       string: Literal -> %;
       empty?: % -> Boolean;

       concat: (Character, %) -> %;
       concat: (%, Character) -> %;
       concat: (%, %) -> %;
       set!: (%, SingleInteger, Character) -> ();
       new: (SingleInteger, Character) -> %;
       new: (NonNegativeInteger, Character) -> %;
       #: % -> SingleInteger;

       =: (%, %) -> Boolean;
}
== add {
   import from SingleInteger;
   import from Character;
   import from Integer;
   import from NonNegativeInteger;
   Rep ==> LString;
   import from Rep;
   import from Integer;

   string(l: Literal): % == per string l;
   empty?(x: %): Boolean == #x = 0;

   #(x: %): SingleInteger == length rep x;

   (a: %) = (b: %): Boolean == rep(a) = rep(b);

   concat(a: %, b: %): % == { 
   	     s := new(# a + # b, char " "); 
	     copy!(s, a, 0, # a); 
	     copy!(s, b, # a, # b);
	     s}

   copy!(dest: %, src: %, offset: SingleInteger, nChars: SingleInteger): () == {
   	    i: SingleInteger := 0;
   	    while (i < nChars) repeat {
	       dest.(i+offset) := src.i;
	       i := i+1;
	    }
   }

   concat(char: Character, string: %): % == {
     result := new(1+#string, char);
     copy!(result, string, 1, #string);
     result
   }
   concat(string: %, char: Character): % == {
     result := new(1+#string, char);
     copy!(result, string, 0, #string);
     result
   }

   new(n: NonNegativeInteger, c: Character): % == per NEW(n::Integer::SingleInteger, c);
   new(n: SingleInteger, c: Character): % == per NEW(n, c);

   set!(s: %, i: SingleInteger, c: Character): () == QESET(rep s, i, c);
   apply(s: %, i: SingleInteger): Character == QENUM(rep s, i);
   char(s: %): Character == s.0;
}
