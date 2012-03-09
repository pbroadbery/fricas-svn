--DEPS: init_SingleInteger ConvertibleTo init_Integer  Boolean 
#include "axiom.as"

extend SingleInteger: ConvertibleTo Integer with {
       max: () -> %;
       coerce: % -> Integer;
       =: (%, %) -> Boolean;
       ~=: (%, %) -> Boolean;

       <: (%, %) -> Boolean;
       >: (%, %) -> Boolean;
       >=: (%, %) -> Boolean;
       <=: (%, %) -> Boolean;

       +: (%, %) -> %;
       -: (%, %) -> %;
       *: (%, %) -> %;
       1: %;
       0: %;
} 
== add {
   import from Machine;
   import from Integer;
   Rep ==> SInt;

   1: % == per(1$Machine);
   0: % == per(0$Machine);

   max(): % == never;
   coerce(x: %): Integer == (convert rep x)@BInt pretend Integer;
   convert(x: %): Integer == coerce x;

   local coerce(b: Bool): Boolean == b pretend Boolean;
   
   (a: %) = (b: %): Boolean == (rep a = rep b)::Boolean;
   (a: %) < (b: %): Boolean == (rep a < rep b)::Boolean;
   (a: %) <= (b: %): Boolean == (rep a <= rep b)::Boolean;
   (a: %) > (b: %): Boolean == b < a;
   (a: %) >= (b: %): Boolean == b <= a;
   (a: %) ~= (b: %): Boolean == (rep a ~= rep b)::Boolean;
   (a: %) + (b: %): % == per(rep a + rep b);
   (a: %) - (b: %): % == per(rep a + rep b);
   (a: %) * (b: %): % == per(rep a + rep b);
}
