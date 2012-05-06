--DEPS: runtime/lisp/Local sexpr/SExpressionCategory Symbol 
--DEPS: init_OutputForm DoubleFloat Integer String List

#include "axiom.as"
#pile
import from System
import from String

SExpression: with
        eq:        (%,%) -> Boolean
          ++ eq(s, t) is true if EQ(s,t) is true in Lisp.
        =:        (%,%) -> Boolean
          ++ eq(s, t) is true if EQUAL(s,t) is true in Lisp.
        null?:     % -> Boolean
          ++ null?(s) is true if s is the S-expression ().
        atom?:     % -> Boolean
          ++ atom?(s) is true if s is a Lisp atom.
        pair?:     % -> Boolean
          ++ pair?(s) is true if s has is a non-null Lisp list.
        list?:     % -> Boolean
          ++ list?(s) is true if s is a Lisp list, possibly ().
        string?:   % -> Boolean
          ++ string?(s) is true if s is an atom and belong to Str.
        symbol?:   % -> Boolean
          ++ symbol?(s) is true if s is an atom and belong to Symbol.
        integer?:  % -> Boolean
          ++ integer?(s) is true if s is an atom and belong to Integer.
        float?:    % -> Boolean
          ++ float?(s) is true if s is an atom and belong to DoubleFloat.
        destruct:  % -> List %
          ++ destruct((a1,...,an)) returns the list [a1,...,an].
        string:    % -> String
          ++ string(s) returns s as an element of String.
          ++ Error: if s is not an atom that also belongs to String.
        symbol:    % -> Symbol
          ++ symbol(s) returns s as an element of Symbol.
          ++ Error: if s is not an atom that also belongs to Symbol.
        integer:   % -> Integer
          ++ integer(s) returns s as an element of Integer.
          ++ Error: if s is not an atom that also belongs to Integer.
        float:     % -> DoubleFloat
          ++ float(s) returns s as an element of DoubleFloat;
          ++ Error: if s is not an atom that also belongs to DoubleFloat.
        convert:   List % -> %
          ++ convert([a1,...,an]) returns the S-expression \spad{(a1,...,an)}.
        convert:   String    -> %
          ++ convert(x) returns the Lisp atom x;
        convert:   Symbol    -> %
          ++ convert(x) returns the Lisp atom x.
        convert:   Integer    -> %
          ++ convert(x) returns the Lisp atom x.
        convert:   DoubleFloat    -> %
          ++ convert(x) returns the Lisp atom x.
        car:       % -> %
          ++ car((a1,...,an)) returns a1.
        cdr:       % -> %
          ++ cdr((a1,...,an)) returns \spad{(a2,...,an)}.
        cons: (%, %) -> %
        #:       % -> Integer
          ++ #((a1,...,an)) returns n.
        elt:       (%, Integer)      -> %
          ++ elt((a1,...,an), i) returns \spad{ai}.
        elt:       (%, List Integer) -> %
          ++ elt((a1,...,an), [i1,...,im]) returns \spad{(a_i1,...,a_im)}.
        nil: %
        eql: (%, %) -> Boolean
        concat: (a: %, b: %) -> %;

 	unparse: % -> String;
== add 
   import from Machine
   default a, b: %
   local ptrrep(a: %): Ptr == a pretend Ptr;
   local ptrper(p: Ptr): % == p pretend %;

   import 
      EQ:    (%, %) -> Boolean
      EQL:   (%, %) -> Boolean
      EQUAL: (%, %) -> Boolean
      NULL:    % -> Boolean
      ATOMP:   % -> Boolean
      BOOT_:_:PAIRP:   % -> Boolean
      STRINGP: % -> Boolean
      BOOT_:_:IDENTP:  % -> Boolean
      INTEGERP: % -> Boolean
      FLOATP: % -> Boolean
      CONS: (%, %) -> %
      CAR: % -> %
      CDR: % -> %
    from Foreign Lisp;

   local IDENTP(a: %): Boolean == BOOT_:_:IDENTP(a);
   local PAIRP(a: %): Boolean == BOOT_:_:PAIRP(a);
   eq(a, b): Boolean == EQ(a, b)
   null? a: Boolean == NULL a
   atom? a: Boolean == ATOMP a
   pair? a: Boolean == PAIRP a
   list? a: Boolean == PAIRP a or NULL a
   string? a: Boolean == STRINGP a
   symbol? a: Boolean == IDENTP a
   integer? a: Boolean == INTEGERP a
   float? a: Boolean == FLOATP a

   destruct b: List % == (list? b    => b pretend List %; error "Non-list")
   string b: String == (STRINGP(b) => b pretend String;error "Non-string")
   symbol b: Symbol == (IDENTP(b) => b pretend Symbol;error "Non-symbol")
   float   b: DoubleFloat == (FLOATP(b)  => b pretend DoubleFloat;error "Non-float")
   integer b: Integer == (INTEGERP(b) => b pretend Integer;error "Non-integer")

   convert(l: List %): % == l pretend %;

   convert(s: String): % == s pretend %
   convert(s: Symbol): % == s pretend %
   convert(i: Integer): % ==  i pretend %
   convert(f: DoubleFloat): % == f pretend %

   nil: % == ptrper(nil$Machine)
   car a: % == CAR a
   cdr a: % == CDR a

   cons(a, b): % == CONS(a, b)
   #(a: %): Integer == never;

   elt(a: %, n: Integer): % == never;
   elt(a: %, n: List Integer): % == never;

   eql(a: %, b: %): Boolean == EQL(a, b)

   concat(a: %, b: %): % == concat(concat, a, b);
   concat(f: (%, %) -> %, a: %, b: %): % == 
      pair? a => cons(car a, f(cdr a, b))
      null? a => b
      never

   (a: %) = (b: %): Boolean == EQUAL(a, b)

   -- Grossly inefficient (needs a buffer type)
   unparse(a: %): String == unparse(unparse, a);

   local unparse(recUnparse: % -> String, a: %): String == 
      import from Symbol
      null? a => "()";
      string? a => concat("_"", concat(string a, "_""))
      symbol? a => name symbol a
      integer? a => string integer a
      float? a => "ddd"
      not pair? a => never
      s := "("
      sep := ""
      while pair? a repeat
         s := concat(s, concat(sep, recUnparse(car a)))
	 a := cdr a
	 sep := " "
      null? a => concat(s, ")");
      s := concat(s, concat(" . ", recUnparse a));
      s := concat(s, ")");
      s

   
