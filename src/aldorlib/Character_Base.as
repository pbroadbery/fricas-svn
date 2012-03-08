--DEPS: init_Character Integer SingleInteger runtime/c/Local String
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

       char(s): % == CHAR_-AT(s, 0)$StringLisp

       (a: %) = (b: %): Boolean == (rep(a) = rep(b))::Boolean;

       ord(c): Integer == never;
       quote(): % == char "'";
       space(): % == char " ";
       newline(): % == char " _
";