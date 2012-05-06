
local LSInteger: with {
   0: %;
   string: % -> String;
   integer: Literal -> %;
   coerce: % -> SInt$Machine;
   coerce: % -> Integer;
   coerce: Integer -> %;

   <: (%, %) -> Boolean;
   >: (%, %) -> Boolean;
   >=: (%, %) -> Boolean;
   <=: (%, %) -> Boolean;
}
== add {
  import from Machine;
  Rep ==> SInt$Machine;
  0: % == per 0;
  
  import { formatSInt: SInt -> String } from Foreign;

  integer(l: Literal): % == per convert(l pretend Arr);
  coerce(n: %): SInt$Machine == rep n;
  coerce(n: %): Integer == (convert rep n)@BInt pretend Integer;
  coerce(n: Integer): % == per convert(n pretend BInt);
  string(a: %): String == { formatSInt rep a }
  
  (<)(a: %, b: %): Boolean == (rep a < rep b) pretend Boolean;
  (>)(a: %, b: %): Boolean == b > a;
  (<=)(a: %, b: %): Boolean == (rep a <= rep b) pretend Boolean;
  (>=)(a: %, b: %): Boolean == b <= a;
}

