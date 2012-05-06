--DEPS: sexpr/SExpressionCategory runtime/c/XLisp System String OutputForm Symbol
#include "axiom.as"

#pile
import from System
import from String

default Str, Sym, Int, Flt, Expr: SetCategory

SExpressionOf(Str, Sym, Int, Flt, Expr): Decl == Body where

    Decl ==> SExpressionCategory(Str, Sym, Int, Flt, Expr)

    Body ==> add
    	default b, b1, b2: %
	import from XLisp;
        dotex: OutputForm := INTERN(lisp(String)("."))$XLisp pretend OutputForm;
	import from Integer;

        coerce(b:%):OutputForm ==
	    import from List OutputForm
	    import from List %
	    import from NonNegativeInteger
	    import from Symbol
            null? b => paren(empty()@OutputForm)
            atom? b => b pretend OutputForm
            r := b
            while not atom? r repeat r := cdr r
            l1 := [b1::OutputForm for b1 in (l := destruct b)]
            not null? r =>
              paren blankSeparate concat!(l1, [dotex, r::OutputForm])
	    qq: OutputForm := outputForm(#"QUOTE")
            (#l)::Integer = 2 and (first(l1) = qq)@Boolean => quote first rest l1
            paren blankSeparate l1

        Rep ==> XLisp
	import from Rep;
        b1 = b2: Boolean        == EQUAL(rep b1,rep b2)$XLisp
        eq(b1, b2): Boolean     == EQ(rep b1, rep b2)$XLisp

        null? b: Boolean      == NULL(rep b)$XLisp
        atom? b: Boolean      == ATOM(rep b)$XLisp
        pair? b: Boolean      == PAIRP(rep b)$XLisp

        list?    b: Boolean   == PAIRP(rep b)$XLisp or NULL(rep b)$XLisp
        string?  b: Boolean   == STRINGP(rep b)$XLisp
        symbol?  b: Boolean   == IDENTP(rep b)$XLisp
        integer? b: Boolean   == INTEGERP(rep b)$XLisp
        float?   b: Boolean   == FLOATP(rep b)$XLisp

        destruct b: List % == (list? b    => b pretend List %; error "Non-list")
        string b: Str == (STRINGP(rep b)$XLisp=> b pretend Str;error "Non-string")
        symbol b: Sym == (IDENTP(rep b)$XLisp => b pretend Sym;error "Non-symbol")
        float   b: Flt == (FLOATP(rep b)$XLisp  => b pretend Flt;error "Non-float")
        integer b: Int == (INTEGERP(rep b)$XLisp => b pretend Int;error "Non-integer")
        expr    b: Expr == b pretend Expr

        convert(l:  List %): % == l  pretend %
        convert(st: Str): %    == st pretend %
        convert(sy: Sym): %    == sy pretend %
        convert(n:  Int): %    == n  pretend %
        convert(f:  Flt): %    == f  pretend %
        convert(e:  Expr): %   == e  pretend %

        car b: %        == per(CAR(rep b)$XLisp)
        cdr b: %        == per(CDR(rep b)$XLisp)
        #   b: Integer  == LENGTH(rep b)$XLisp pretend Integer

        elt(b:%, i:Integer): %       == never;
        elt(b:%, li:List Integer): % == never;
--        elt(b:%, i:Integer): %       == destruct(b).i
--        elt(b:%, li:List Integer): % ==
--          for i in li repeat b := destruct(b).i
--          b
