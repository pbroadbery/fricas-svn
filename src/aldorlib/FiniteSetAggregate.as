--DEPS: Dictionary SetCategory finiteAggregate SetAggregate Finite
--DEPS: NonNegativeInteger_SemiRing Integer_IntegralDomain
--DEPS: OrderedSemiRingSegment List_StreamAggregate
#include "axiom.as"
#pile

import from String
import from System

FiniteSetAggregate(S:SetCategory): Category ==
  Join(Dictionary S, SetAggregate S, finiteAggregate) with
    cardinality: % -> NonNegativeInteger
      ++ cardinality(u) returns the number of elements of u.
      ++ Note: \axiom{cardinality(u) = #u}.
    if S has Finite then
      Finite
      complement: % -> %
        ++ complement(u) returns the complement of the set u,
        ++ i.e. the set of all values not in u.
      universe: () -> %
        ++ universe()$D returns the universal set for finite set aggregate D.
    if S has OrderedSet then
      max: % -> S
        ++ max(u) returns the largest element of aggregate u.
      min: % -> S
        ++ min(u) returns the smallest element of aggregate u.
    parts: % -> List S
        ++ parts(u) returns a list of the consecutive elements of u.
        ++ For collections, \axiom{parts([x,y,...,z]) = (x,y,...,z)}.
	++ TODO: This is really a bug, as HomogeneousAggregate has 
	++ the same function declared, conditional on '% has finiteAggregate
    default 
     import from NonNegativeInteger
     default s, t: %
     default l: List S

     s <= t: Boolean          == s = intersect(s,t)
     s < t:  Boolean           == #s < #t and s <= t
     s = t: Boolean           == #s = #t and empty? difference(s,t)
     brace l: %         == construct l
     set   l: %         == construct l
     cardinality s: NonNegativeInteger   == #s
     construct l: %     == (s := set(); for x in l repeat insert!(x,s); s)
     count(x:S, s:%): NonNegativeInteger == (member?(x, s) => 1; 0)
     subset?(s, t): Boolean   ==
         #s < #t and every?((x : S) : Boolean +-> member?(x, t), parts s)
  
     coerce(s:%):OutputForm ==
       brace([x::OutputForm for x in parts s]$List(OutputForm))
  
     intersect(s, t): % ==
       i := set()
       for x in parts s | member?(x, t) repeat insert!(x, i)
       i
  
     difference(s:%, t:%): % ==
       m := copy s
       for x in parts t repeat remove!(x, m)
       m
  
     symmetricDifference(s, t): % ==
      if not(% has finiteAggregate) then s
      else
       d := copy s
       for x in parts t repeat
         if member?(x, s) then remove!(x, d) else insert!(x, d)
       d
  
     union(s:%, t:%): % ==
        u := copy s
        for x in parts t repeat insert!(x, u)
        u
  
     import from S
     if S has Finite then
       import from OrderedSemiRingSegment NonNegativeInteger
       import from PositiveInteger
       import from Integer
       universe(): %   == set([index(i::PositiveInteger) for i in 1..size()$S])
       complement s: % == difference(universe(), s )
       size(): NonNegativeInteger == (2 ^ size()$S)::NonNegativeInteger

-- TODO: Make this work
--         set([index(j::PositiveInteger)$S for j in 1..size()$S | bit?(i-1,j-1)])
  
       lookup s: PositiveInteger ==
         import from List S
	 import from Integer
         n:PositiveInteger := 1
         for x in parts s repeat
	     q := lookup(x)
             n := n + (2 ^ ((q - 1)::NonNegativeInteger))::PositiveInteger
         n

     import from List S
     if S has OrderedSet then
       max s: S ==
         empty?(l := parts s) => error "Empty set"
         reduce(max, l)
  
       min s: S ==
         empty?(l := parts s) => error "Empty set"
         reduce(min, l)
  
  