--DEPS: SetCategory init_List init_Boolean Integer
#include "axiom.as"

#pile
default Str, Sym, Int, Flt, Expr: SetCategory
SExpressionCategory(Str, Sym, Int, Flt, Expr): Category == Decl where
    Decl ==> SetCategory with
        eq:        (%,%) -> Boolean
          ++ eq(s, t) is true if EQ(s,t) is true in Lisp.
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
          ++ symbol?(s) is true if s is an atom and belong to Sym.
        integer?:  % -> Boolean
          ++ integer?(s) is true if s is an atom and belong to Int.
        float?:    % -> Boolean
          ++ float?(s) is true if s is an atom and belong to Flt.
        destruct:  % -> List %
          ++ destruct((a1,...,an)) returns the list [a1,...,an].
        string:    % -> Str
          ++ string(s) returns s as an element of Str.
          ++ Error: if s is not an atom that also belongs to Str.
        symbol:    % -> Sym
          ++ symbol(s) returns s as an element of Sym.
          ++ Error: if s is not an atom that also belongs to Sym.
        integer:   % -> Int
          ++ integer(s) returns s as an element of Int.
          ++ Error: if s is not an atom that also belongs to Int.
        float:     % -> Flt
          ++ float(s) returns s as an element of Flt;
          ++ Error: if s is not an atom that also belongs to Flt.
        expr:      % -> Expr
          ++ expr(s) returns s as an element of Expr;
          ++ Error: if s is not an atom that also belongs to Expr.
        convert:   List % -> %
          ++ convert([a1,...,an]) returns the S-expression \spad{(a1,...,an)}.
        convert:   Str    -> %
          ++ convert(x) returns the Lisp atom x;
        convert:   Sym    -> %
          ++ convert(x) returns the Lisp atom x.
        convert:   Int    -> %
          ++ convert(x) returns the Lisp atom x.
        convert:   Flt    -> %
          ++ convert(x) returns the Lisp atom x.
        convert:   Expr   -> %
          ++ convert(x) returns the Lisp atom x.
        car:       % -> %
          ++ car((a1,...,an)) returns a1.
        cdr:       % -> %
          ++ cdr((a1,...,an)) returns \spad{(a2,...,an)}.
        #:       % -> Integer
          ++ #((a1,...,an)) returns n.
        elt:       (%, Integer)      -> %
          ++ elt((a1,...,an), i) returns \spad{ai}.
        elt:       (%, List Integer) -> %
          ++ elt((a1,...,an), [i1,...,im]) returns \spad{(a_i1,...,a_im)}.
