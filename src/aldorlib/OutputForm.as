--DEPS: init_OutputForm init_List String Integer Symbol init_DoubleFloat init_NonNegativeInteger
--DEPS: NumberFormats Character_Base OutputFormLisp SetCategory
#include "axiom"

#pile

extend OutputForm: SetCategory with
        --% Printing
        print  : % -> ()
          ++ print(u) prints the form u.
        message: String -> %
          ++ message(s) creates an form with no string quotes
          ++ from string s.
        messagePrint: String -> ()
          ++ messagePrint(s) prints s without string quotes. Note:
          ++ \spad{messagePrint(s)} is equivalent to \spad{print message(s)}.
        --% Creation of atomic forms
        outputForm: Integer -> %
          ++ outputForm(n) creates an form for integer n.
        outputForm: Symbol  -> %
          ++ outputForm(s) creates an form for symbol s.
        outputForm: String  -> %
          ++ outputForm(s) creates an form for string s.
        outputForm: DoubleFloat  -> %
          ++ outputForm(sf) creates an form for small float sf.
        empty   : () -> %
          ++ empty() creates an empty form.

        --% Sizings
        width: % -> Integer
          ++ width(f) returns the width of form f (an integer).
        height: % -> Integer
          ++ height(f) returns the height of form f (an integer).
        width: % -> Integer
          ++ width() returns the width of the display area (an integer).
        height: % -> Integer
          ++ height() returns the height of the display area (an integer).
        subHeight: % -> Integer
          ++ subHeight(f) returns the height of form f below the base line.
        superHeight: % -> Integer
          ++ superHeight(f) returns the height of form f above the base line.
         --% Space manipulations
        hspace: Integer -> %  ++ hspace(n) creates white space of width n.
        vspace: Integer -> %  ++ vspace(n) creates white space of height n.
        rspace: (Integer,Integer) -> %
          ++ rspace(n,m) creates rectangular white space, n wide by m high.
        --% Area adjustments
        left: (%,Integer) -> %
          ++ left(f,n) left-justifies form f within space of width n.
        right: (%,Integer) -> %
          ++ right(f,n) right-justifies form f within space of width n.
        center: (%,Integer) -> %
          ++ center(f,n) centers form f within space of width n.
        left: % -> %
          ++ left(f) left-justifies form f in total space.
        right: % -> %
          ++ right(f) right-justifies form f in total space.
        center:   % -> %
          ++ center(f) centers form f in total space.

        --% Area manipulations
        hconcat:  (%,%) -> %
          ++ hconcat(f,g) horizontally concatenate forms f and g.
        vconcat:  (%,%) -> %
          ++ vconcat(f,g) vertically concatenates forms f and g.
        hconcat:  List % -> %
          ++ hconcat(u) horizontally concatenates all forms in list u.
        vconcat:  List % -> %
          ++ vconcat(u) vertically concatenates all forms in list u.

        --% Application formers
        prefix:  (%, List %) -> %
          ++ prefix(f,l) creates a form depicting the n-ary prefix
          ++ application of f to a tuple of arguments given by list l.
        infix:   (%, List %) -> %
          ++ infix(f,l) creates a form depicting the n-ary application
          ++ of infix operation f to a tuple of arguments l.
        infix:   (%, %, %) -> %
          ++ infix(op, a, b) creates a form which prints as: a op b.
        postfix: (%, %)    -> %
          ++ postfix(op, a)  creates a form which prints as: a op.
        infix?: % -> Boolean
          ++ infix?(op) returns true if op is an infix operator,
          ++ and false otherwise.
        elt:     (%, List %) -> %
          ++ elt(op,l) creates a form for application of op
          ++ to list of arguments l.

        --% Special forms
        string:  % -> %
          ++ string(f) creates f with string quotes.
        label:   (%, %) -> %
          ++ label(n,f) gives form f an equation label n.
        box:     % -> %
          ++ box(f) encloses f in a box.
        matrix:  List List % -> %
          ++ matrix(llf) makes llf (a list of lists of forms) into
          ++ a form which displays as a matrix.
        zag:     (%, %) -> %
          ++ zag(f,g) creates a form for the continued fraction form for f over g.
        root:    % -> %
          ++ root(f) creates a form for the square root of form f.
        root:    (%, %) -> %
          ++ root(f,n) creates a form for the nth root of form f.
        over:    (%, %) -> %
          ++ over(f,g) creates a form for the vertical fraction of f over g.
        slash:   (%, %) -> %
          ++ slash(f,g) creates a form for the horizontal fraction of f over g.
        assign:  (%, %) -> %
          ++ assign(f,g) creates a form for the assignment \spad{f := g}.
        rarrow:  (%, %) -> %
          ++ rarrow(f,g) creates a form for the mapping \spad{f -> g}.
--        differentiate: (%, NonNegativeInteger) -> %
          ++ differentiate(f,n) creates a form for the nth derivative of f,
          ++ e.g. \spad{f'}, \spad{f''}, \spad{f'''},
          ++ "f super \spad{iv}".
        binomial: (%, %) -> %
          ++ binomial(n,m) creates a form for the binomial coefficient of n and m.
        tensor:  (%, %) -> %
          ++ tensor(a,b) creates a form for a tensor b

        --% Scripts
        sub:     (%, %) -> %
          ++ sub(f,n) creates a form for f subscripted by n.
        super:   (%, %) -> %
          ++ super(f,n) creates a form for f superscripted by n.
        presub:  (%, %) -> %
          ++ presub(f,n) creates a form for f presubscripted by n.
        presuper:(%, %) -> %
          ++ presuper(f,n) creates a form for f presuperscripted by n.
        scripts: (%, List %) -> %
            ++ \spad{scripts(f, [sub, super, presuper, presub])}
            ++  creates a form for f with scripts on all 4 corners.
        supersub:(%, List %) -> %
            ++ supersub(a,[sub1,super1,sub2,super2,...])
            ++ creates a form with each subscript aligned
            ++ under each superscript.

        --% Diacritical marks
        quote:   % -> %
          ++ quote(f) creates the form f with a prefix quote.
        dot:     % -> %
          ++ dot(f) creates the form with a one dot overhead.
        dot:     (%, NonNegativeInteger) -> %
          ++ dot(f,n) creates the form f with n dots overhead.
        prime:   % -> %
          ++ prime(f) creates the form f followed by a suffix prime (single quote).
        prime:   (%, NonNegativeInteger) -> %
          ++ prime(f,n) creates the form f followed by n primes.
        overbar: % -> %
          ++ overbar(f) creates the form f with an overbar.
        overlabel: (%, %) -> %
          ++ overlabel(x,f) creates the form f with "x overbar" over the top.

        --% Plexes
        sum:     (%)       -> %
          ++ sum(expr) creates the form prefixing expr by a capital sigma.
        sum:     (%, %)    -> %
          ++ sum(expr,lowerlimit) creates the form prefixing expr by
          ++ a capital sigma with a lowerlimit.
        sum:     (%, %, %) -> %
          ++ sum(expr,lowerlimit,upperlimit) creates the form prefixing expr by
          ++ a capital sigma with both a lowerlimit and upperlimit.
        prod:    (%)       -> %
          ++ prod(expr) creates the form prefixing expr by a capital pi.
        prod:    (%, %)    -> %
          ++ prod(expr,lowerlimit) creates the form prefixing expr by
          ++ a capital pi with a lowerlimit.
        prod:    (%, %, %) -> %
          ++ prod(expr,lowerlimit,upperlimit) creates the form prefixing expr by
          ++ a capital pi with both a lowerlimit and upperlimit.
        int:     (%)       -> %
          ++ int(expr) creates the form prefixing expr with an integral sign.
        int:     (%, %)    -> %
          ++ int(expr,lowerlimit) creates the form prefixing expr by an
          ++ integral sign with a lowerlimit.
        int:     (%, %, %) -> %
          ++ int(expr,lowerlimit,upperlimit) creates the form prefixing expr by
          ++ an integral sign with both a lowerlimit and upperlimit.

        --% Matchfix forms
        brace:   % -> %
          ++ brace(f) creates the form enclosing f in braces (curly brackets).
        brace:   List % -> %
          ++ brace(lf) creates the form separating the elements of lf
          ++ by commas and encloses the result in curly brackets.
        bracket: % -> %
          ++ bracket(f) creates the form enclosing f in square brackets.
        bracket: List % -> %
          ++ bracket(lf) creates the form separating the elements of lf
          ++ by commas and encloses the result in square brackets.
        paren:   % -> %
          ++ paren(f) creates the form enclosing f in parentheses.
        paren:   List % -> %
          ++ paren(lf) creates the form separating the elements of lf
          ++ by commas and encloses the result in parentheses.

        --% Separators for aggregates
        pile:     List % -> %
          ++ pile(l) creates the form consisting of the elements of l which
          ++ displays as a pile, i.e. the elements begin on a new line and
          ++ are indented right to the same margin.

        commaSeparate: List % -> %
          ++ commaSeparate(l) creates the form separating the elements of l
          ++ by commas.
        semicolonSeparate:  List % -> %
          ++ semicolonSeparate(l) creates the form separating the elements of l
          ++ by semicolons.
        blankSeparate: List % -> %
          ++ blankSeparate(l) creates the form separating the elements of l
          ++ by blanks.
        --% Specific applications
        =:     (%, %) -> %
          ++ f = g creates the equivalent infix form.
        ~=:    (%, %) -> %
          ++ f ~= g creates the equivalent infix form.
        <:     (%, %) -> %
          ++ f < g creates the equivalent infix form.
        >:     (%, %) -> %
          ++ f > g creates the equivalent infix form.
        <=:    (%, %) -> %
          ++ f <= g creates the equivalent infix form.
        >=:    (%, %) -> %
          ++ f >= g creates the equivalent infix form.
        +:     (%, %) -> %
          ++ f + g creates the equivalent infix form.
        -:     (%, %) -> %
          ++ f - g creates the equivalent infix form.
        -:     (%)    -> %
          ++ - f creates the equivalent prefix form.
        *:     (%, %) -> %
          ++ f * g creates the equivalent infix form.
        /:     (%, %) -> %
          ++ f / g creates the equivalent infix form.
        ^:    (%, %) -> %
          ++ f ^ g creates the equivalent infix form.
        rem:   (%, %) -> %
          ++ f rem g creates the equivalent infix form.
        quo:   (%, %) -> %
          ++ f quo g creates the equivalent infix form.
        exquo: (%, %) -> %
          ++ exquo(f,g) creates the equivalent infix form.
        _and:   (%, %) -> %
          ++ f and g creates the equivalent infix form.
        _or:    (%, %) -> %
          ++ f or g creates the equivalent infix form.
        _not:   (%)    -> %
          ++ not f creates the equivalent prefix form.
        SEGMENT: (%,%)  -> %
          ++ SEGMENT(x,y) creates the infix form: \spad{x..y}.
        SEGMENT: (%)    -> %
          ++ SEGMENT(x) creates the prefix form: \spad{x..}.

    == add
        import from NumberFormats

        -- Todo:
        --   program forms, greek letters
        --   infix, prefix, postfix, matchfix support in OUT BOOT
        --   labove rabove, corresponding overs.
        --   better super script, overmark, undermark
        --   bug in product, paren blankSeparate []
        --   uniformize integrals, products, etc as plexes.
	Rep ==> XLisp;
	import from XLisp;
        cons(a, b) ==> per(CONS(rep a, b pretend XLisp)$XLisp)
        car  ==> CAR$XLisp
        cdr  ==> CDR$XLisp

        default a, b, c, x: %
        default l: List %
        default s: String
        default e: Symbol
        default n, m, w, h: Integer
        default nn:NonNegativeInteger
        default ll: List List %
	
	import from Character
        --sform:    String  -> %
        --eform:    Symbol  -> %
        --iform:    Integer -> %

        print x: ()              == mathprint(x)$OutputFormLisp
        message s: %            == (empty? s => empty(); s pretend %)
        messagePrint s: ()       == print message s
        (a:%) = (b:%):Boolean  == EQUAL(rep a, rep b)$XLisp
        (a:%) = (b:%):%        == convert [eform #"=",     a, b]
        coerce(a):OutputForm  == a pretend OutputForm

	convert(l: List %): % == never;

        outputForm n: %         == n pretend %
        outputForm e: %         == e pretend %
        outputForm(f:DoubleFloat): % == f pretend %
        local sform s: %               == s pretend %
        local eform e: %               == e pretend %
        local iform n: %                == n pretend %

        outputForm s: % ==
          sform concat(quote()$Character, concat(s, quote()$Character))

        width(a): Integer == outformWidth(a)$OutputFormLisp
        height(a): Integer == height(a)$OutputFormLisp
        subHeight(a): Integer == subspan(a)$OutputFormLisp
        superHeight(a): Integer == superspan(a)$OutputFormLisp
        height(): Integer == 20
        width(): Integer == 66

        center(a,w): %   == hconcat(hspace((w - width(a)) quo 2),a)
        left(a,w): %     == hconcat(a,hspace((w - width(a))))
        right(a,w): %    == hconcat(hspace(w - width(a)),a)
        center(a): %     == center(a,width())
        left(a): %       == left(a,width())
        right(a): %      == right(a,width())

        vspace(n): % ==
          n = 0 => empty()
          vconcat(sform " ",vspace(n - 1))

        hspace(n): % ==
          n = 0 => empty()
          sform(fillerSpaces(n, " ")$OutputFormLisp)

        rspace(n, m): % ==
          n = 0 or m = 0 => empty()
          vconcat(hspace n, rspace(n, m - 1))

        matrix ll: % ==
            lv: List % := [per(LIST2VEC(l pretend XLisp)) for l in ll]
            per CONS(rep eform #"MATRIX", LIST2VEC(lv pretend XLisp))

        pile l: %              == cons(eform #"SC", l)
        commaSeparate l: %     == cons(eform #"AGGLST",  l)
        semicolonSeparate l: % == cons(eform #"AGGSET",  l)

        blankSeparate l: %     ==
           c:=eform #"CONCATB"
           l1: List % := []
           for u in reverse l repeat
               if EQCAR(rep u,rep c)$XLisp
                  then l1:=concat(cdr(rep u) pretend List %, l1) -- [:cdr u,:l1] 
                  else l1:=concat(u, l1)
           cons(c, l1)

        brace a: %        == convert [eform #"BRACE", a]
        brace l: %        == brace commaSeparate l
        bracket a: %      == convert [eform #"BRACKET", a]
        bracket l: %      == bracket commaSeparate l
        paren a: %        == convert [eform #"PAREN", a]
        paren l: %        == paren commaSeparate l

        sub(a, b): %  == convert [eform #"SUB", a, b]
        super(a, b): % == convert [eform #"SUPERSUB", a, sform " ", b]
        presub(a, b): % == convert [eform #"SUPERSUB", a, sform " ", sform " ",_
                                  sform " ", b]
        presuper(a, b): % == convert [eform #"SUPERSUB", a, sform " ", sform " ", b]
        scripts(a, l): % ==
            null l => a
            null rest l => sub(a, first l)
            cons(eform #"SUPERSUB", cons(a, l))
        supersub(a, l): % ==
            if odd?(#l) then l := append(l, [empty()])
            cons(eform #"ALTSUPERSUB", cons(a, l))

        hconcat(a, b): %  == convert [eform #"CONCAT", a, b]
        hconcat l: %     == cons(eform #"CONCAT", l)
        vconcat(a, b): %  == convert [eform #"VCONCAT", a, b]
        vconcat l: %     == cons(eform #"VCONCAT", l)

        a ~= b: %      == convert [eform #"~=",    a, b]
        a < b: %       == convert [eform #"<",     a, b]
        a > b: %       == convert [eform #">",     a, b]
        a <= b: %      == convert [eform #"<=",    a, b]
        a >= b: %      == convert [eform #">=",    a, b]

        a + b: %       == convert [eform #"+",     a, b]
        a - b: %       == convert [eform #"-",     a, b]
        - a: %         == convert [eform #"-",     a]
        a * b: %       == convert [eform #"*",     a, b]
        a / b: %       == convert [eform #"/",     a, b]
        a ^ b: %      == convert [eform #"^",    a, b]
        a rem b: %     == convert [eform #"rem",   a, b]
        a quo b: %     == convert [eform #"quo",   a, b]
        a exquo b: %   == convert [eform #"exquo", a, b]
        _and(a, b): %     == convert [eform #"and",   a, b]
        _or(a, b): %      == convert [eform #"or",    a, b]
        _not(a): %       == convert [eform #"not",   a]
        SEGMENT(a, b): % == convert [eform #"SEGMENT", a, b]
        SEGMENT(a): %  == convert [eform #"SEGMENT", a]
        binomial(a, b): % == convert [eform #"BINOMIAL", a, b]

        empty(): % == convert [eform #"NOTHING"]

        infix? a: Boolean == false
--            elt: % :=
--                IDENTP(a)$XLisp => a
--                STRINGP(a)$XLisp => INTERN(a)$XLisp
--                return false
--            if GET(elt,QUOTE(INFIXOP$XLisp)$XLisp)$XLisp then true else false

        elt(a, l): % == cons(a, l)

        prefix(a,l): % ==
            not infix? a => cons(a, l)
            hconcat(a, paren commaSeparate l)
	    
        infix(a, l): % ==
            null l => empty()
            null rest l => first l
            infix? a => cons(a, l)
            hconcat [first l, a, infix(a, rest l)]
        infix(a,b,c): %  ==
            infix? a => convert [a, b, c]
            hconcat [b, a, c]
        postfix(a, b): % ==
            hconcat(b, a)

        add__prime(a : %, b : %) : % == convert [eform #"PRIME", a, b]
        string a: %   == convert [eform #"STRING",  a]
        quote  a: %   == convert [eform #"QUOTE",   a]
        overbar a: %  == convert [eform #"OVERBAR", a]
        dot a: %      == super(a, sform ".")
        prime a: %    == prime(a, 1)
        dot(a,nn): %   == (s := new(nn, char "."); super(a, sform s))
        prime(a, nn): % == (s := new(nn, char ",");  add__prime(a, sform s))

        overlabel(a,b): % == convert [eform #"OVERLABEL", a, b]
        box a: %      == convert [eform #"BOX",     a]
        zag(a,b): %   == convert [eform #"ZAG",     a, b]
        root a: %     == convert [eform #"ROOT",    a]
        root(a,b): %  == convert [eform #"ROOT",    a, b]
        over(a,b): %  == convert [eform #"OVER",    a, b]
        slash(a,b): % == convert [eform #"SLASH",   a, b]
        assign(a,b): %== convert [eform #"LET",     a, b]

        label(a,b): % == convert [eform #"EQUATNUM", a, b]
        rarrow(a,b): %== convert [eform #"TAG", a, b]

-- Delayed until we need it.	
--        differentiate(a, nn): % ==
--            zero? nn => a
--            nn::Integer < 4 => prime(a, nn)
--            r := FormatRoman(nn::PositiveInteger)
--            s := lowerCase(r::String)
--            add__prime(a, paren sform s)

        sum(a): %     == convert [eform #"SIGMA",  empty(), a]
        sum(a,b): %   == convert [eform #"SIGMA",  b, a]
        sum(a,b,c): % == convert [eform #"SIGMA2", b, c, a]
        prod(a): %    == convert [eform #"PI",     empty(), a]
        prod(a,b): %  == convert [eform #"PI",     b, a]
        prod(a,b,c): %== convert [eform #"PI2",    b, c, a]
        int(a): %     == convert [eform #"INTSIGN",empty(), empty(), a]
        int(a,b): %   == convert [eform #"INTSIGN",b, empty(), a]
        int(a,b,c): % == convert [eform #"INTSIGN",b, c, a]
        tensor(a,b): %== convert [eform #"TENSOR",a,b]


