)package "BOOT"

DEFPARAMETER($prev_line_number, 0)
DEFPARAMETER($curent_line_number, 0)
DEFPARAMETER($prev_line, nil)
DEFPARAMETER($curent_line, nil)

DEFPARAMETER($compiler_InteractiveFrame,
             addBinding('$DomainsInScope,
                    [["FLUID", :true],
                      ["special", :(COPY_-TREE $InitialDomainsInScope)]],
                    addBinding('$Information, nil,
                                makeInitialModemapFrame())))

DEFPARAMETER($NONBLANK, nil)

set_nonblank(val) == SETF($NONBLANK, val)

current_line_number() ==
    tok := CURRENT_-TOKEN()
    tok =>
         pos := TOKEN_-NONBLANK(tok)
         pos and INTEGERP(pos) => pos
         nil
    nil

spad_syntax_error(wanted, parsing) ==
    SPAD_ERROR_LOC(true)
    if $prev_line then
        FORMAT(true, '"~&The prior line was:~%~%~5D> ~A~%~%",
           $prev_line_number, $prev_line)
    if $curent_line then
        FORMAT(true, '"~&The current line is:~%~%~5D> ~A~%~%",
           $curent_line_number, $curent_line)
    TOKEN_-STACK_-SHOW()
    THROW('SPAD_READER, nil)

fakeloopInclude(name, n) ==
    handle_input_file(name, function fakeloopInclude0, [name, n])


DEFPARAMETER($COMBLOCKLIST, nil)
DEFPARAMETER($docList, nil)
DEFVAR($spad_scanner, false)
DEFVAR($restore_list, nil)


spadCompile(name) ==
    $comp370_apply : local := FUNCTION PRINT_-DEFUN
    _*FILEACTQ_-APPLY_* : local := FUNCTION PRINT_-DEFUN
    _*EOF_* : local := false
    _/EDITFILE : local := name
    $InteractiveMode : local := false
    $spad_scanner : local := true
    $COMBLOCKLIST : local := nil
    $docList : local := nil
    $curent_line_number := 0
    $prev_line := nil
    $InteractiveFrame : local := $compiler_InteractiveFrame
    $MacroTable := MAKE_-HASH_-TABLE()
    $restore_list := nil
    a := ncloopIncFileName name
    res := fakeloopInclude(name, nil)
    true

DEFPARAMETER($toklst, nil)

$trans_table := [["id", "IDENTIFIER"], ["key", "KEYWORD"], _
                  ["string", "SPADSTRING"], ["char", "SPADSTRING"], _
                  ["integer", "NUMBER"], ["float", "SPADFLOAT"]]

-- ["BREAK", "leave"], _
$trans_key := [ _
                ["ARROW", "->"], _
                ["AT", "@"], _
                ["BAR", "|"], _
                ["BECOMES", ":="], _
                ["CARAT", "^"], _
                ["COERCE", "::"], _
                ["COLON", ":"], _
                ["COMMA", ","], _
                ["DEF", "=="], _
                ["DOT", "."], _
                ["EQUAL", "="], _
                ["EXIT", "=>"], _
                ["GE", ">="], _
                ["GIVES", "+->"], _
                ["GT", ">"], _
                ["LE", "<="], _
                ["LT", "<"], _
                ["MDEF", "==>"], _
                ["MINUS", "-"], _
                ["NOTEQUAL", "~="], _
                ["PLUS", "+"], _
                ["SEG", ".."], _
                ["SEMICOLON", ";"], _
                ["SLASH", "/"], _
                ["TIMES", "*"], _
                ["BACKSET", ";"]]

$trans_key_id := [ _
                ["break", "break"], _
                ["DEFAULT", "default"], _
                ["RULE", "rule"], _
                ["fooo", "baaar"] _
                ]

DEFVAR($paren_level)
DEFVAR($settab_level)
DEFVAR($tab_states)
DEFVAR($ignored_tab)
DEFVAR($ignorable_backset)

ntokreader(token) ==
    nonblank_flag := nil
    set_nonblank(nil)
    if $toklst then
        tok1 := first $toklst
        $toklst := rest $toklst
        type1 := first(tok1)
        sym := tok1.1
        pos := tok1.4
        line_info := first(rest(pos))
        line_no := first(rest(rest(line_info)))
        if not($curent_line_number = line_no) then
            $prev_line := $curent_line
            $prev_line_number := $curent_line_number
            $curent_line := line_info.1
            $curent_line_number := line_no
        if type1 = "integer" and STRINGP(sym) then
            sym := READ_-FROM_-STRING(sym)
        if type1 = "float" then
            mant_i := READ_-FROM_-STRING(first(sym))
            exp := READ_-FROM_-STRING(sym.2)
            mant_fl := #(sym.1)
            mant_f := READ_-FROM_-STRING(sym.1)
            sym := make_float(mant_i, mant_f, mant_fl, exp)
        if sym = "(" and type1 = "key" and tok1.3 = "nonblank" then
            nonblank_flag := true
            set_nonblank(true) 
        type := ASSQ(type1, $trans_table)
        greater_SI($paren_level, 0) and type1 = "key" and _
          sym in ["BACKSET", "BACKTAB", "SETTAB"] =>
            if sym = "SETTAB" then
                $settab_level := inc_SI($settab_level)
            if sym = "BACKTAB" then
                $settab_level := dec_SI($settab_level)
            ntokreader(token)
        greater_SI($settab_level, 0) and type1 = "key" and sym = "BACKTAB" =>
            $settab_level := dec_SI($settab_level)
            ntokreader(token)
        -- Fix bad piles 
        if type1 = "key" and sym = "BACKSET" and $toklst then
            ntok1 := first $toklst
            ntype1 := first(ntok1)
            nsym := ntok1.1
            if ntype1 = "key" and nsym in ["then", "else"] then
                return ntokreader(token)
        type1 = "key" and sym = "BACKSET" and $ignorable_backset =>
            ntokreader(token)
        if type1 = "key" and sym in ["[", "COMMA", "SEMICOLON"] then
            $ignorable_backset := true
        else
            $ignorable_backset := false
        if type1 = "key" and sym = "SETTAB" and $toklst then
            ntok1 := first $toklst
            ntype1 := first(ntok1)
            nsym := ntok1.1
            if ntype1 = "key" and nsym in ["then", "else",
                  "COMMA", "SEMICOLON"] then
                PUSH($ignored_tab, $tab_states)
                $ignored_tab := true
                return ntokreader(token)
            else
                PUSH($ignored_tab, $tab_states)
                $ignored_tab := false
        if type1 = "key" and sym = "BACKSET" and $ignored_tab then
            return ntokreader(token)
        if type1 = "key" and sym = "BACKTAB" then
            $ignored_tab0 := $ignored_tab
            $ignored_tab := POP($tab_states)
            if $ignored_tab0 then
                return ntokreader(token)
        if type then
            type := type.1
        else
            SAY([sym, type1])
        if type1 = "key" then
            sym = "(" =>
                $paren_level := inc_SI($paren_level)
            sym = ")" =>
                $paren_level := dec_SI($paren_level)
            sym = "#1" => type := "ARGUMENT-DESIGNATOR"
            sym1 := ASSQ(sym, $trans_key)
            sym2 := ASSQ(sym, $trans_key_id)
            if sym2 then
                type := "IDENTIFIER"
                sym1 := sym2
            sym :=
                sym1 => sym1.1
                sym
        TOKEN_-INSTALL(sym, type, token, line_no)
    else
        TOKEN_-INSTALL(nil, "*EOF", token, nil)

DEFVAR($token_reader)

fakeloopInclude0(st, name, n) ==
    $lines : local := incStream(st, name)
    $token_reader := function ntokreader
    fakeloopProcess(n,
      next(function insertpile,
        next(function lineoftoks,$lines)))
    nil

fakeloopProcess1(tok_list) ==
    $toklst := tok_list
    $paren_level := 0
    $settab_level := 0
    $tab_states := nil
    $ignored_tab := false
    $ignorable_backset := false
    finish_comment()
    TOKEN_-STACK_-CLEAR()
    parse_new_expr()
    parseout := pop_stack_1()
    if parseout then S_process(parseout)
    nil


processSymbol(s) ==
    sym1 := first s
    pos := first(rest(sym1))
    npos := rest rest pos
    rest rest sym1 => [first sym1, rest s, npos, "nonblank", pos]
    [first sym1, rest s, npos, false, pos]

processCommand(line) ==
    cl := rest(line)
    InterpExecuteSpadSystemCommand(cl)

fakeloopProcess(n, s) ==
    StreamNull s => nil
    lp := first s
    line := first first lp
    kind := first first first line
    kind = "command" =>
        processCommand(first(line))
        fakeloopProcess(n, rest s)
    nline := [processSymbol(sym) for sym in line]
    fakeloopProcess1(nline)
    fakeloopProcess(n, rest s)
