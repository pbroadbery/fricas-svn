--DEPS: SetCategory DictionaryOperations NonNegativeInteger_OrderedAbelianMonoidSup
--DEPS: List_StreamAggregate
#include "axiom.as"

#pile

Dictionary(S:SetCategory): Category ==
  DictionaryOperations S
 with
  default
   import from List S
   import from NonNegativeInteger

   default l: List S
   default s, t: %
   dictionary l: % ==
     d := dictionary()
     for x in l repeat insert!(x, d)
     d

   if % has finiteAggregate then
    -- remove(f:S->Boolean,t:%)  == remove!(f, copy t)
    -- select(f, t)        == select!(f, copy t)
     select!(f: S -> Boolean, t: %): %      == remove!((x : S) : Boolean +-> not f(x), t)

     --extract! d ==
     --  empty? d => error "empty dictionary"
     --  remove!(x := first parts d, d, 1)
     --  x

     s = t: Boolean ==
       eq?(s,t) => true
       #s ~= #t => false
       every?((x: S): Boolean +-> member?(x, t), parts s)

     remove!(f:S->Boolean, t:%): % ==
       for m in parts t repeat if f m then remove!(m, t)
       t
