--DEPS: Dictionary SetCategory Finite
#include "axiom.as"
#pile

FSA(S:SetCategory): Category ==
  Dictionary S with
--    if S has Finite then
    Finite
    parts: % -> List S
        ++ parts(u) returns a list of the consecutive elements of u.
        ++ For collections, \axiom{parts([x,y,...,z]) = (x,y,...,z)}.
	++ TODO: This is really a bug, as HomogeneousAggregate has 
	++ the same function declared, conditional on '% has finiteAggregate
    default 
     default s: %

     if S has Finite then
       lookup s: PositiveInteger ==
         import from List S
	 import from Integer
         n:PositiveInteger := 1
         for x in parts s repeat
	     q := lookup(x)
         n

