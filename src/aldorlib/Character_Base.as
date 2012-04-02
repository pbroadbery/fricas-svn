--DEPS: init_Character Integer SingleInteger runtime/ARCH/Local String
#include "axiom.as"

#pile

extend Character: with 
       char: String -> %
       =: (%, %) -> Boolean
       ord: % -> Integer
       quote: () -> %;
       space: () -> %;
       newline: () -> %;
  == add
       Rep ==> Char$Machine;
       import from Machine;

       import from Integer
       default s: String
       default a, b, c: %
       import from SingleInteger;

       local coerce(flg: Bool): Boolean == flg pretend Boolean;

       char(s): % == s.0;

       (a: %) = (b: %): Boolean == (rep(a) = rep(b))::Boolean;

       ord(c): Integer == never;
       quote(): % == char "_"";
       space(): % == char " ";
       newline(): % == char " _
";