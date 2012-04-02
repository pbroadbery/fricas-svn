--DEPS: init_String init_Character init_List Integer runtime/ARCH/Local 
--DEPS: SingleInteger NonNegativeInteger
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

       set!: (%, SingleInteger, Character) -> ();
       apply: (%, SingleInteger) -> Character;
       string: Integer -> %;

       =: (%, %) -> Boolean;

       print: % -> ();
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
   	    offset < 0 => never;
	    #dest < offset + nChars => never;
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

   new(n: NonNegativeInteger, c: Character): % == {
       new(n::Integer::SingleInteger, c);
   }
   new(n: SingleInteger, c: Character): % == {
       s := per NEW(n);
       i: SingleInteger := 0;
       while i < n repeat {
       	     s.i := c;
	     i := i+1;
       }
       s
   }

   set!(s: %, i: SingleInteger, c: Character): () == QESET(rep s, i, c);
   apply(s: %, i: SingleInteger): Character == QENUM(rep s, i);
   char(s: %): Character == s.0;

   string(n: Integer): % == per string n;

   print(s: %): () == {
   	    import from IO;
	    print rep s; 
	    nl: Rep := "_
";
	    print nl;
   }
}
