--DEPS: OrderedAbelianMonoidSup IndexedDirectProductCategory
--DEPS: NonNegativeInteger_OrderedAbelianMonoidSup
--DEPS: IndexedDirectProductObject
--DEPS: Integer_OrderedRing

#include "axiom.as"

#pile
import from Boolean

IndexedExponents(Varset: OrderedSet): Join(OrderedAbelianMonoidSup,
            IndexedDirectProductCategory(NonNegativeInteger,Varset))
==
 IndexedDirectProductObject(NonNegativeInteger, Varset) add
      Term ==  Record(k:Varset, c:NonNegativeInteger)
      Rep ==  List Term
      import from Rep;
      default x:%
      default t:Term

      import from OutputForm
      import from Integer
      import from List OutputForm

      local null(x: %): Boolean == null rep(x)
      local rest(x: %): % == per rest rep(x)
      local first(x: %): Term == first rep(x)

      coerceOF(t):OutputForm ==     --++ converts term to OutputForm
         t.c = 1 => (t.k)::OutputForm
         (t.k)::OutputForm ^ (t.c)::OutputForm

      +++ converts entire exponents to OutputForm
      coerce(x):OutputForm == 
         null x => 1@Integer::OutputForm
         null rest x => coerceOF(first x)
         reduce(*,[coerceOF t for t in x])

