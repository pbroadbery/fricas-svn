--DEPS:  HomogeneousAggregate 
#include "axiom.as"

import from Boolean;

RecursiveAggregate(S:Type): Category == HomogeneousAggregate(S) with {
   children: % -> List %;
     ++ children(u) returns a list of the children of aggregate u.
   -- should be % -> %* and also needs children: % -> Iterator(S,S)
   nodes: % -> List %;
     ++ nodes(u) returns a list of all of the nodes of aggregate u.
   -- to become % -> %* and also nodes: % -> Iterator(S,S)
   leaf?: % -> Boolean;
     ++ leaf?(u) tests if u is a terminal node.
   value: % -> S;
     ++ value(u) returns the value of the node u.
   elt: (%,'value') -> S;
     ++ elt(u,"value") (also written: \axiom{a. value}) is
     ++ equivalent to \axiom{value(a)}.
   cyclic?: % -> Boolean;
     ++ cyclic?(u) tests if u has a cycle.
   leaves: % -> List S;
     ++ leaves(t) returns the list of values in obtained by visiting the
     ++ nodes of tree \axiom{t} in left-to-right order.
   distance: (%,%) -> Integer;
     ++ distance(u,v) returns the path length (an integer) from node u to v.
   if S has SetCategory then {
      child?: (%,%) -> Boolean;
        ++ child?(u,v) tests if node u is a child of node v.
      node?: (%,%) -> Boolean;
        ++ node?(u,v) tests if node u is contained in node v
        ++ (either as a child, a child of a child, etc.).
   }
   if % has shallowlyMutable then {
      setchildren!: (%,List %)->%;
        ++ setchildren!(u,v) replaces the current children of node u
        ++ with the members of v in left-to-right order.
      setelt: (%,'value',S) -> S;
        ++ setelt(a,"value",x) (also written \axiom{a . value := x})
        ++ is equivalent to \axiom{setvalue!(a,x)}
      setvalue!: (%,S) -> S;
        ++ setvalue!(u,x) sets the value of node u to x.
   }
default {
   import from List %;
   import from List S;
   default x, l: %;
   default y: S;
   elt(x,v: 'value'): S == value x;

   if % has shallowlyMutable then
     setelt(x,v: 'value',y): S == setvalue!(x,y);

   if S has SetCategory then
       child?(x,l): Boolean == member?(x, children(l));

   if % has finiteAggregate then
       parts(x): List S == [value(i) for i in nodes(x)];
}
}
