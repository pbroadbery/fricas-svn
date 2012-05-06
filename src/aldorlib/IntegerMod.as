--DEPS: CommutativeRing ConvertibleTo Integer_IntegralDomain StepThrough Finite SingleInteger
#include "axiom.as"
import from Boolean;

IntegerMod(p:PositiveInteger):
 Join(CommutativeRing, Finite, ConvertibleTo Integer, StepThrough) == add {
  default x, y: %;
  import from Integer;
  import from SingleInteger;
  size(): NonNegativeInteger  == p::NonNegativeInteger;
  characteristic(): NonNegativeInteger == p::NonNegativeInteger;
  lookup x: PositiveInteger == (zero? x => p; (convert(x)@Integer) :: PositiveInteger);

-- Code is duplicated for the optimizer to kick in.
--  if p::Integer <= convert(max()$SingleInteger)@Integer then {
--    Rep== SingleInteger;
--    q := p::SingleInteger;
--
--    bloodyCompiler: Integer -> %;
--    bloodyCompiler(n: Integer): % == positiveRemainder(n, p::Integer)$Integer pretend %;
--
--    convert(x:%):Integer == convert(x)$Rep;
--    coerce(x):OutputForm == never;
--    coerce(n:Integer):%  == bloodyCompiler n;
--    0: %                    == 0$Rep;
--    1: %                    == 1$Rep;
--    init: %                 == 0$Rep;
--    nextItem(n: %): Partial %  == {
--                              m:=n+1;
--                              m=0 => failed();
--                              m}
--    x = y: Boolean                == x =$Rep y;
--    (x:%) * (y:%): %     == mulmod(x, y, q);
--    (n:Integer) * (x:%): % == mulmod(bloodyCompiler n, x, q);
--    x + y: %                == addmod(x, y, q);
--    x - y: %                == submod(x, y, q);
--    random(): %             == random(q)$Rep;
--    index a: %              == positiveRemainder(a::%, q);
--    -x: %                  == (zero? x => 0; q -$Rep x);
--
--    (x:%) ^ (n:NonNegativeInteger): % == {
--      n < p => powmod(x, n::Rep, q);
--      powmod(convert(x)@Integer, n, p)$Integer :: Rep;
--    }
--    recip x: % =={
--       (c1, c2, g) := extendedEuclidean(x, q)$Rep;
----       not one? g => "failed";
--       not (g = 1) => "failed";
--       positiveRemainder(c1, q);}
--  }
--  else {
  
    Rep== Integer;
    default a: PositiveInteger;
    default x, y: %;
    import from Rep;
    convert(x:%):Integer == rep x;
    coerce(n:Integer):%  == per positiveRemainder(n, p::Integer);
    coerce(x):OutputForm == coerce(rep x)$Rep;
    sample(): % == per 0;
    0: %                    == per 0;
    1: %                    == per 1;
    init(): %                 == 0;
    nextItem(n: %): Partial %          =={
                              m:=n+1;
                              m=0 => failed();
                              success(m)}
    x = y: Boolean                == rep(x) = rep(y);
    (x:%) * (y:%): %            == per mulmod(rep x, rep y, p::Integer);
    (n:Integer) * (x:%): %      == per mulmod(positiveRemainder(n, p::Integer), rep x, p::Integer);
    x + y: %             == per addmod(rep x, rep y, p::Integer);
    x - y: %             == per submod(rep x, rep y, p::Integer);
    random(): %          == per(random(p::Integer)$Rep);
    index a: %           == per positiveRemainder(a::Integer, p::Integer);
    - x: %               == per (zero? x => 0; (p::Integer) - rep(x));
    (x:%) ^ (n:NonNegativeInteger): % == per powmod(rep x, n::Rep, p::Integer);

    recip x: Partial % == {
       (c1, c2, g) := extendedEuclidean(rep x, p::Integer);
--       not one? g => "failed";
       not (g = 1) => failed();
       success(per positiveRemainder(c1, p::Integer))}
--  }
}