--DEPS: SetCategory BagAggregate Collection String_SetCategory
#include "axiom.as"

#pile

DictionaryOperations(S:SetCategory): Category ==
  Join(BagAggregate S, Collection(S)) with
   dictionary: () -> %
     ++ dictionary()$D creates an empty dictionary of type D.
   dictionary: List S -> %
     ++ dictionary([x,y,...,z]) creates a dictionary consisting of
     ++ entries \axiom{x,y,...,z}.
-- insert: (S,%) -> S                 ++ insert an entry
-- member?: (S,%) -> Boolean                  ++ search for an entry
-- remove!: (S,%,NonNegativeInteger) -> %
--   ++ remove!(x,d,n) destructively changes dictionary d by removing
--   ++ up to n entries y such that \axiom{y = x}.
-- remove!: (S->Boolean,%,NonNegativeInteger) -> %
--   ++ remove!(p,d,n) destructively changes dictionary d by removing
--   ++ up to n entries x such that \axiom{p(x)} is true.
   if % has finiteAggregate then
     remove!: (S,%) -> %
       ++ remove!(x,d) destructively changes dictionary d by removing
       ++ all entries y such that \axiom{y = x}.
     remove!: (S->Boolean,%) -> %
       ++ remove!(p,d) destructively changes dictionary d by removeing
       ++ all entries x such that \axiom{p(x)} is true.
     select!: (S->Boolean,%) -> %
       ++ select!(p,d) destructively changes dictionary d by removing
       ++ all entries x such that \axiom{p(x)} is not true.
   default
     default l: List S
     import from String

     construct l: % == dictionary l
     dictionary(): % == empty()

     if % has finiteAggregate then
       copy(d: %): % == dictionary parts d

       coerce(s:%):OutputForm ==
         import from List OutputForm
         prefix("dictionary"@String :: OutputForm,
                                      [x::OutputForm for x in parts s])

