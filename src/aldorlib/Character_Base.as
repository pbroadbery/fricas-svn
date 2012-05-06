--DEPS: init_Character Integer SingleInteger XLisp String
#include "axiom.as"

#pile

extend Character: with 
       char: String -> %
       =: (%, %) -> Boolean
       ord: % -> Integer
       quote: () -> %;
       space: () -> %;
  == add
       import from Integer
       import from XLisp
       default s: String
       default a, b, c: %

       crep(a) ==> lisp(%)(a)
       char(s): % == unlisp(%)(CHAR_-AT(lisp(String)(s), 0))

       (a: %) = (b: %): Boolean == EQUAL(crep(a), crep(b))

       ord(c): Integer == never;
       quote(): % == char "'";
       space(): % == char " ";
