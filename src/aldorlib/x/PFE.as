--DEPS: init_List
#include "axiom.as"
#pile

#if 0
P==>List %
define PFE: Category == with
     sqFree: P -> List P
     zzz: () -> Solver %

Solver(R: PFE): with
	  solve: List R -> List List R
== add
   solve(p: List R): List List R == never
#endif
