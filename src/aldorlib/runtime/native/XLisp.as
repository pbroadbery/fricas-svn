--DEPS: lang init_Boolean init_XLisp init_Pointer Integer 
--DEPS: init_SingleInteger init_Character init_List init_PrimitiveArray
--DEPS: runtime/c/LString

#include "axiom.as"

extend XLisp: with {
   EQ: (%, %) -> Boolean;
   T: () -> %;
   NIL: () -> %;
   NULL: % -> Boolean;
   ATOM: % -> Boolean;
   PAIRP: % -> Boolean;
   STRINGP: % -> Boolean;
   INTEGERP: % -> Boolean;
--   FLOATP: % -> Boolean;
--   IDENTP: % -> Boolean;
   
   CONS: (%, %) -> %;
   CAR: % -> %;
   CDR: % -> %;
   RPLACA: (%, %) -> ();
   RPLACD: (%, %) -> ();
--   LENGTH: % -> %;
   EQUAL: (%, %) -> Boolean;
   EQ: (%, %) -> Boolean;
   EQCAR: (%, %) -> Boolean;


--   INTERN: % -> %;

--   NUMBERP: % -> Boolean;
--   READ_-FROM_-STRING: % -> %;

   STRINGIMAGE: % -> %;
   PARSE_-INTEGER: % -> %;
   LIST2VEC: % -> %;
   0: %;

--   lisp: (T: with) -> T -> %;
   lisp: (T: with) -> T -> %;
   unlisp: (T: with) -> % -> T;

   PRINT: % -> ();
   PRINT0: % -> ();

   EQL: (%, %) -> Boolean;
   QENUM: (%, SingleInteger) -> Character;
   QESET: (%, SingleInteger, Character) -> ();
   QSLESSP: (%, %) -> Boolean;
   QSGREATERP: (%, %) -> Boolean;
   MAKE_-FULL_-CVEC: (SingleInteger, Character) -> %;
   QCSIZE: String -> SingleInteger;

   CHAR_-AT: (s: String, n: SingleInteger) -> Character;

} == add {
   import from Machine;

   Rep ==> Union(nil: Pointer, array: LArray, pair: LPair, string: LString, other: LDepCross, integer: Integer);
   import from Rep;
   import from LPair;
   import from LDepCross;
   import from LString;
   import from LArray;
   import from LSInteger;

   EQ(a: %, b: %): Boolean == (rep(a) pretend Ptr$Machine = rep(b) pretend Ptr$Machine) pretend Boolean;
   T(): % == NIL(); --FIXME
   NIL(): % == per [nil$Machine pretend Pointer];
   NULL(p: %): Boolean == rep(p) case nil;
   ATOM(p: %): Boolean == not(rep(p) case pair);
   PAIRP(p: %): Boolean == rep(p) case pair;
   STRINGP(p: %): Boolean == rep(p) case string;
   INTEGERP(p: %): Boolean == rep(p) case integer;
--   FLOATP(p: %): Boolean == rep(p) case float;
--   IDENTP(p: %): Boolean == rep(p) case symbol;
   
   CAR(p: %): % == car(rep(p).pair);
   CDR(p: %): % == cdr(rep(p).pair);
   CONS(p: %, q: %): % == per [cons(p, q)];
   RPLACA(p: %, v: %): () == setcar!(rep(p).pair, v);
   RPLACD(p: %, v: %): () == {import from IO; print "rplacd"; CHKPAIR(p); setcdr!(rep(p).pair, v);}

   EQCAR(p: %, q: %): Boolean == EQ(CAR(p), q);

   CHKPAIR(p: %): () == { PRINT p; assert(PAIRP p);}

   0: % == per [0];

   PARSE_-INTEGER(x: %): % == never;
   STRINGIMAGE(x: %): % == never;
   LIST2VEC(x: %): % == never;
   EQUAL(p: %, q: %): Boolean == never;
   QVMAXINDEX(a: %): % == never;
   QVSIZE(a: %): % == per [#(rep(a).array)::Integer];
   QAREF1(a: %, b: %): % == get(rep(a).array, (rep(b).integer)::LSInteger);
   QSETAREF1(a: %, b: %, c: %): % == {set(rep(a).array, (rep(b).integer)::LSInteger, c); a}
   MAKE_-ARRAY(a: %): % == per [new((rep(a).integer)::LSInteger, NIL())];
   MAKEARR1(a: %, b: %): % == per [new((rep(a).integer)::LSInteger, b)];

   -- STRINGS

   EQL(a: %, b: %): Boolean == never;

   QSLESSP(a: %, b: %): Boolean == never;
   QSGREATERP(a: %, b: %): Boolean == never;
   QENUM(a: %, b: SingleInteger): Character == QENUM(rep(a).string, b)$LString;
   QESET(a: %, b: SingleInteger, c: Character): () == QESET(rep(a).string, b, c)$LString;
   MAKE_-FULL_-CVEC(n: SingleInteger, c: Character): % == per [NEW(n, c)$LString];
   
   CHAR_-AT(s: String, n: SingleInteger): Character == QENUM(s pretend LString, n);
   QCSIZE(s: String): SingleInteger == length(s pretend LString);
   --
   -- PRINTING
   -- 
   PRINT(a: %): () == {
       import from IO;
       import from LCharacter;
       PRINT0 a;
       print newline();
   }

   PRINT0(a: %): () == {
       import from IO;
       rep(a) case string => {print "string-"; print rep(a).string;}
       rep(a) case integer => {print "int-"; print string(rep(a).integer);}
       rep(a) case pair => printList a;
       rep(a) case other => print "other";
       never;
   }


  local printList(p: %): () == { 
  	  import from LString;
	  import from IO;
  	  print "(";
  	  while PAIRP p repeat {
	  	PRINT0 CAR p;
		print " ";
	  	p := CDR p;
	  }
	  if (not NULL p) then { print " . "; PRINT0 CDR p}
	  print ")";
  }

   X == Cross(T: with, T);
   lisp(T: with)(t: T): % == {
   	   import from LDepCross;
 	   import from IO;
   	   T has TheString => per [t pretend LString];
   	   T has TheInteger => per [t pretend Integer];
   	   T has TheList => t pretend %;
   	   T has TheArray => per [t pretend LArray];
	   print "other~";
	   per [new(T, t pretend T)];
   }

   unlisp(T: with)(a: %): T == {
   	     import from IO;
   	     import from Machine;
   	     nil?(a pretend Ptr$Machine) pretend Boolean => never;
      	     print "unlisp";
   	     rep(a) case string => {
	     	    print "string!";
	     	    not (T has TheString) => never;
		    rep(a).string pretend T;
             }
   	     rep(a) case integer => {
	     	    print "integer!";
	     	    not(T has TheInteger) => never;
		    rep(a).integer pretend T;
             }
   	     rep(a) case array => {
	     	    print "array!";
	     	    not(T has TheArray) => { print "oopps"; never;}
		    x := rep(a).array pretend T;
	     	    print "done!";
		    x
             }
	     rep(a) case pair => a pretend T;
	     rep(a) case nil => a pretend T;

             print "other!";
	     depcross := rep(a).other;	     
	     (Q, q) == value depcross;
	     q pretend T;
   }

}

LCharacter: with {
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
       fputss: (Bytes, SingleInteger, SingleInteger, P) -> ();
       fputc: (LCharacter, P) -> ();
       stdoutFile: () -> P;
   } from Foreign C;
   import from LSInteger;
   import from LString;

   print(s: LString): () == fputss(bytes s, 0 pretend SingleInteger, length s, stdoutFile());
   print(c: LCharacter): () == fputc(c, stdoutFile());
   print(n: SingleInteger): () == print string(n)
}

LDepCross: with {
   new: (A: with, A) -> %;
   value: % -> (T: with, T);
} 
== add {
   Rep ==> Cross(T: with, T);
   import from Rep;

   new(A: with, a: A): % == { c := (A, a); c pretend %; }
   value(a: %): (T: with, t: T) == rep a;
}

LPair: with {
      cons: (XLisp, XLisp) -> %;
      car: % -> XLisp;
      cdr: % -> XLisp;
      setcar!: (%, XLisp) -> ();
      setcdr!: (%, XLisp) -> ();
} 
== add {
  Rep ==> Record(car: XLisp, cdr: XLisp);
  import from IO;
  import from Rep;

  cons(a: XLisp, b: XLisp): % == per [a, b];

  car(p: %): XLisp == rep(p).car;
  cdr(p: %): XLisp == rep(p).cdr;
  
  setcar!(p: %, v: XLisp): () == rep(p).car := v;
  setcdr!(p: %, v: XLisp): () == rep(p).cdr := v;
}

