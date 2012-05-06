--DEPS:  init_String init_Character init_List Integer
#include "axiom"

extend String: with {
       string: Literal -> %;
       empty?: % -> Boolean;
       new: (NonNegativeInteger, Character) -> %;
       concat: (Character, %) -> %;
       concat: (%, Character) -> %;
       concat: (%, %) -> %;
       minIndex: % -> Integer;
       maxIndex: % -> Integer;
       set!: (%, Integer, Character) -> Character;
}
== add {
   lrep(x) ==> lisp(%)(x);
   lper(x) ==> unlisp(%)(x);

   string(x: Literal): % == never;
   empty?(x: %): Boolean == never;

   minIndex(x: %): Integer == 0;
   maxIndex(x: %): Integer == #x - 1;

   map(f: Character -> Character, s: %): % == never;
   
   split(s: %, c: Character): List % == never;
   concat(l: List %): % == never;
   any?(f: Character -> Boolean, s: %): Boolean == never;
   #(x: %): Integer == never;
   concat(a: %, b: %): % == never;
   concat(a: Character, b: %): % == never;
   concat(a: %, b: Character): % == never;

   new(n: NonNegativeInteger, c: Character): % == never;

   set!(s: %, i: Integer, c: Character): Character == never;
}
