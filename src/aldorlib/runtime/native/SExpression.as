--DEPS: runtime/native/Local sexpr/SExpressionCategory Symbol 
--DEPS: init_OutputForm DoubleFloat Integer String List

#include "axiom.as"
#pile

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
   Cons ==> Record(car: %, cdr: %);
   Rep ==> Union(string: String, symbol: Symbol, integer: Integer, 
                 float: DoubleFloat, pair: Cons);
   import from Rep;
   import from Cons;
   default a, b: %;
   import from Machine;
   import from LPair SExpression;

   local ptrrep(a: %): Ptr == a pretend Ptr;
   local ptrper(p: Ptr): % == p pretend %;

   eq(a, b): Boolean == (ptrrep a = ptrrep b) pretend Boolean;

   null? a: Boolean == (ptrrep a = nil) pretend Boolean;
   
   atom? a: Boolean == not pair? a

   pair? a: Boolean == not null? a and rep a case pair;
   
   list? a: Boolean == null? a or pair? a;

   string? a: Boolean == not null? a and rep(a) case string;
   
   symbol? a: Boolean == not null? a and rep(a) case symbol;

   integer? a: Boolean == not null? a and rep(a) case integer

   float? a: Boolean == not null? a and rep(a) case float;

   destruct a: List % == never;

   string a: String == rep(a).string;
   symbol a: Symbol == rep(a).symbol;
   integer a: Integer == rep(a).integer;
   float a: DoubleFloat == rep(a).float;

   convert(l: List %): % == 
       empty? l => nil
       cons(first l, convert rest l)

   convert(s: String): % == per [s];
   convert(s: Symbol): % == per [s];
   convert(i: Integer): % == per [i];
   convert(f: DoubleFloat): % == per [f];

   nil: % == ptrper(nil$Machine)
   car a: % == rep(a).pair.car;
   cdr a: % == rep(a).pair.cdr;

   cons(a, b): % == per [[a, b]]
   #(a: %): Integer == never;

   elt(a: %, n: Integer): % == never;
   elt(a: %, n: List Integer): % == never;

   eql(a: %, b: %): Boolean == 
      integer? a => integer? b and rep(a).integer = rep(b).integer
      float? a => never
--      float? a => float? b and rep(a).float = rep(b).float
      eq(a, b)

   concat(a: %, b: %): % == 
      pair? a => cons(car a, concat(cdr a, b))
      null? a => b
      never

   (a: %) = (b: %): Boolean == 
      null? a => null? b
      null? b => false
      pair? a => pair? b and car(a) = car(b) and cdr(a) = cdr(b)
      string? a => string? b and string a = string b
      symbol? a => symbol? b and symbol a = symbol b
      integer? a => integer? b and integer a = integer b
      float? a => float? b and float a = float b
      never

   -- Grossly inefficient (needs a buffer type)
   unparse(a: %): String == unparse(unparse, a);

   local unparse(recUnparse: % -> String, a: %): String == 
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
