--DEPS: HomogeneousAggregate shallowlyMutable
#include "axiom.as"

#pile
BagAggregate(S:Type): Category == Join(HomogeneousAggregate S,_
     shallowlyMutable) with
   bag: List S -> %
     ++ bag([x,y,...,z]) creates a bag with elements x,y,...,z.
   extract!: % -> S
     ++ extract!(u) destructively removes a (random) item from bag u.
   insert!: (S,%) -> %
     ++ insert!(x,u) inserts item x into bag u.
   inspect: % -> S
     ++ inspect(u) returns an (random) element from a bag.
   default
    bag(l: List S): % ==
     x: % := empty()
     for s in l repeat x:=insert!(s,x)
     x

