--DEPS:  lang x/init_U SetCategory
#include "axiom"

extend UniversalSegment(S: Type): with { if S has SetCategory then foo: () -> () } == add {
  if S has SetCategory then foo(): () == never;
}

--U2(S: Type): with  { if S has SetCategory then foo: () -> () } == add {
--  if S has SetCategory then foo(): () == never;
--}
