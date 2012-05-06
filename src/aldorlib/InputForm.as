--DEPS: sexpr/SExpressionCategory Any init_InputForm
#include "axiom.as"
#pile

import from Boolean;
import from String;
import from System;

extend InputForm:
  Join(SExpressionCategory(String,Symbol,Integer,DoubleFloat,OutputForm),
       ConvertibleTo SExpression) with
    interpret: % -> Any
      ++ interpret(f) passes f to the interpreter.
    convert  : SExpression -> %
      ++ convert(s) makes s into an input form.
    binary   : (%, List %) -> %
      ++ \spad{binary(op, [a1,...,an])} returns the input form
      ++ corresponding to  \spad{a1 op a2 op ... op an}.
    function : (%, List Symbol, Symbol) -> %
      ++ \spad{function(code, [x1,...,xn], f)} returns the input form
      ++ corresponding to \spad{f(x1,...,xn) == code}.
    lambda   : (%, List Symbol) -> %
      ++ \spad{lambda(code, [x1,...,xn])} returns the input form
      ++ corresponding to \spad{(x1,...,xn) +-> code} if \spad{n > 1},
      ++ or to \spad{x1 +-> code} if \spad{n = 1}.
    +      : (%, %) -> %
      ++ \spad{a + b} returns the input form corresponding to \spad{a + b}.
    *      : (%, %) -> %
      ++ \spad{a * b} returns the input form corresponding to \spad{a * b}.
    /      : (%, %) -> %
      ++ \spad{a / b} returns the input form corresponding to \spad{a / b}.
    ^     : (%, NonNegativeInteger) -> %
      ++ \spad{a ^ b} returns the input form corresponding to \spad{a ^ b}.
    ^     : (%, Integer) -> %
      ++ \spad{a ^ b} returns the input form corresponding to \spad{a ^ b}.
    0        : %
      ++ \spad{0} returns the input form corresponding to 0.
    1        : %
      ++ \spad{1} returns the input form corresponding to 1.
    flatten  : % -> %
      ++ flatten(s) returns an input form corresponding to s with
      ++ all the nested operations flattened to triples using new
      ++ local variables.
      ++ If s is a piece of code, this speeds up
      ++ the compilation tremendously later on.
    unparse  : % -> String
      ++ unparse(f) returns a string s such that the parser
      ++ would transform s to f.
      ++ Error: if f is not the parsed form of a string.
    parse    : String -> %
      ++ parse(s) is the inverse of unparse. It parses a
      ++ string to InputForm
    declare  : List %   -> Symbol
      ++ declare(t) returns a name f such that f has been
      ++ declared to the interpreter to be of type t, but has
      ++ not been assigned a value yet.
      ++ Note: t should be created as \spad{devaluate(T)$Lisp} where T is the
      ++ actual type of f (this hack is required for the case where
      ++ T is a mapping type).
    compile  : (Symbol, List %) -> Symbol
      ++ \spad{compile(f, [t1,...,tn])} forces the interpreter to compile
      ++ the function f with signature \spad{(t1,...,tn) -> ?}.
      ++ returns the symbol f if successful.
      ++ Error: if f was not defined beforehand in the interpreter,
      ++ or if the ti's are not valid types, or if the compiler fails.
 == SExpression add
    Rep == SExpression

    import from String
    import from Integer
    import from List %

    default s1, s2: %;
    default sy: Symbol;
    default signature: List %


    import 
      declare: (Symbol, List %) -> ()
      selectLocalMms: (%, %, List %, List %) -> String;
      unparseInputForm: % -> %
      ncParseFromString: String -> %;
      mkAtree: % -> SExpression;
      transferPropsToNode: (%, SExpression) -> ();
    from Foreign Lisp;

    local mkProperOp: Symbol -> %
    local strsym    : % -> String
    local tuplify   : List Symbol -> %
    
    0: %                        == convert(0@Integer)
    1: %                        == convert(1@Integer)
    convert(x:%):SExpression == x pretend SExpression
    convert(x:SExpression):% == x pretend %

    conv(ll : List %): % ==
      convert(ll pretend List SExpression)$SExpression pretend %

    lambda(f: %,l: List Symbol): % == never;
#if 0
    	      conv([convert("+->"::Symbol),tuplify l,f]$List(%))
#endif

    interpret(x: %): Any == never
#if 0
      v := interpret(x)
      mkObj(unwrap(objVal(v)$Lisp)$Lisp, objMode(v)$Lisp)$Lisp
#endif

    convert(x:DoubleFloat):% == never
#if 0
      zero? x => 0
--      one? x => 1
      (x = 1) => 1
      convert(x)$Rep
#endif

    flatten(s: %): % == never
#if 0
    local flatten0  : (%, Symbol, NonNegativeInteger) ->
                                             Record(lst: List %, symb:%)

    flatten(s: %): % == never      -- will not compile if I use 'or'
      atom? s => s
      every?(atom?,destruct s)$List(%) => s
      sy := new()$Symbol
      n:NonNegativeInteger := 0
      l2 := [flatten0(x, sy, n := n + 1) for x in rest(l := destruct s)]
      conv(concat(convert(#"SEQ")@%,
        concat(concat [u.lst for u in l2], conv(
           [convert(#"exit")@%, 1$%, conv(concat(first l,
               [u.symb for u in l2]))@%]$List(%))@%)))@%

    flatten0(s: %, sy: Symbol, n: NonNegativeInteger): % ==
      atom? s => [nil(), s]
      a := convert(concat(string sy, convert(n)@String)::Symbol)@%
      l2 := [flatten0(x, sy, n := n+1) for x in rest(l := destruct s)]
      [concat(concat [u.lst for u in l2], conv([convert(
        #"LET")@%, a, conv(concat(first l,
             [u.symb for u in l2]))@%]$List(%))@%), a]
#endif
    local strsym(s: %): String == never
#if 0
      string? s => string s
      symbol? s => string symbol s
      error "strsym: form is neither a string or symbol"
#endif

    unparse(x: %): String == never;
#if 0
      import from List String
      atom?(s:% := unparseInputForm(x)) => strsym s
      concat [strsym a for a in destruct s]
#endif

    parse(s:String):% ==
      ncParseFromString(s);

    declare signature: Symbol ==
      declare(name := new()$Symbol, signature)
      name

    compile(name: Symbol, types: List %): Symbol == never
#if 0
      symbol car cdr car _
        selectLocalMms(mkProperOp name, convert(name)@%,
          types, nil()$List(%))
#endif

    mkProperOp(name: Symbol): % == never
#if 0
      op := mkAtree(nme := convert(name)@%)
      transferPropsToNode(nme, op)
      convert op
#endif
    binary(op: %, args: List %): % == never
#if 0
      (n := #args) < 2 => error "Need at least 2 arguments"
      n = 2 => convert([op, first args, last args]$List(%))
      convert([op, first args, binary(op, rest args)]$List(%))
#endif

    tuplify(l: List Symbol): % == never
#if 0
      empty? rest l => convert first l
      conv _
        concat(convert(#"Tuple"), [convert x for x in l]$List(%))
#endif

    function(f: %, l: List Symbol, name: Symbol): % == never
#if 0
      nn := convert(new(1 + #l, convert(nil()$List(%)))$List(%))@%
      conv([convert(#"DEF"), conv(cons(convert(name)@%,
                        [convert(x)@% for x in l])), nn, nn, f]$List(%))
#endif

    s1 + s2: % == never
#if 0
      s1 = 0 => s2
      s2 = 0 => s1
      conv [convert("+"::Symbol), s1, s2]$List(%)
#endif
    s1 * s2: % == never
#if 0
      s1 = 0 or s2 = 0 => 0
      s1 = 1 => s2
      s2 = 1 => s1
      conv [convert("*"::Symbol), s1, s2]$List(%)
#endif

    (s1:%) ^ (n:Integer): % == never
#if 0
      s1 = 0 and n > 0 => 0
      s1 = 1 or zero? n => 1
--      one? n => s1
      (n = 1) => s1
      conv [convert("^"::Symbol), s1, convert n]$List(%)
#endif

    (s1:%) ^ (n:NonNegativeInteger): % == s1 ^ (n::Integer)

    s1 / s2: % == never
#if 0
      s2 = 1 => s1
      conv [convert("/"::Symbol), s1, s2]$List(%)
#endif
