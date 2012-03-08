--DEPS: PositiveInteger Integer Character_Base init_Float String PrimitiveArray_Base Partial List
--DEPS: init_Symbol

#include "axiom.as"

import from String;
#pile

NumberFormats: NFexports == NFimplementation where
    PI ==> PositiveInteger
    I  ==> Integer
    C  ==> Character
    F  ==> Float
    S  ==> String
    V  ==> PrimitiveArray
    NNI ==> NonNegativeInteger

    NFexports ==> with
        FormatArabic: PI -> S
            ++ FormatArabic(n) forms an Arabic numeral
            ++ string from an integer n.
        ScanArabic:   S -> PI
            ++ ScanArabic(s) forms an integer from an Arabic numeral string s.
--        FormatRoman:  PI -> S
            ++ FormatRoman(n) forms a Roman numeral string from an integer n.
--        ScanRoman:    S -> PI
            ++ ScanRoman(s) forms an integer from a Roman numeral string s.
--        ScanFloatIgnoreSpaces: S -> F
            ++ ScanFloatIgnoreSpaces(s) forms a floating point number from
            ++ the string s ignoring any spaces. Error is generated if the
            ++ string is not recognised as a floating point number.
--        ScanFloatIgnoreSpacesIfCan: S -> Partial F
            ++ ScanFloatIgnoreSpacesIfCan(s) tries to form a floating point number from
            ++ the string s ignoring any spaces.


    NFimplementation ==> add
        default pn: PI
	default s: S

--        FormatArabic pn: S == unlisp(S)(STRINGIMAGE(lisp(PI)(pn))$XLisp)
--        ScanArabic   s: PI == unlisp(PI)(PARSE_-INTEGER(lisp(S)(s))$XLisp)
        FormatArabic pn: S == never
        ScanArabic   s: PI == never

