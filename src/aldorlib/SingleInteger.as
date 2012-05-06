--DEPS: init_SingleInteger ConvertibleTo Integer
#include "axiom.as"

extend SingleInteger: ConvertibleTo Integer with {
       max: () -> %;
       coerce: % -> Integer;
       =: (%, %) -> Boolean;
       <: (%, %) -> Boolean;
       +: (%, %) -> %;
       -: (%, %) -> %;
       *: (%, %) -> %;
       integer: Literal -> %;
       1: %;
} 
== add {
   import from Integer;
   1: % == never;
   max(): % == never;
   coerce(x: %): Integer == never;
   convert(x: %): Integer == never;

   coerce: PositiveInteger -> %;
   
   (a: %) = (b: %): Boolean == never;
   (a: %) < (b: %): Boolean == never;
   (a: %) ~= (b: %): Boolean == never;
   (a: %) + (b: %): % == never;
   (a: %) - (b: %): % == never;
   (a: %) * (b: %): % == never;
   integer(l: Literal): % == never;
}
