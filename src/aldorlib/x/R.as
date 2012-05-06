--DEPS:  List
#include "axiom.as"

import from Boolean;
xyzzy: with == add;

RecursiveAggregate(S:Type): Category == with {
   children: % -> List %;
     ++ children(u) returns a list of the children of aggregate u.

   if S has SetCategory then {
      SetCategory;
      child?: (%,%) -> Boolean;
        ++ child?(u,v) tests if node u is a child of node v.
   }
default {
   import from List %;
   default x, l: %;

   if S has SetCategory then
       child?(x,l): Boolean == member?(x, children(l));

}
}
