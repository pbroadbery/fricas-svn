--DEPS:  SetCategory shallowlyMutable Eltable
#include "axiom.as"

import from Boolean;
#pile
EltableAggregate(Dom:SetCategory, Im:Type): Category ==
-- This is separated from Eltable
-- and series won't have to support qelt's and setelt's.
  Eltable(Dom, Im) with
    elt : (%, Dom, Im) -> Im
    elt : (%, Dom, Im) -> Im
       ++ elt(u, x, y) applies u to x if x is in the domain of u,
       ++ and returns y otherwise.
       ++ For example, if u is a polynomial in \axiom{x} over the rationals,
       ++ \axiom{elt(u,n,0)} may define the coefficient of \axiom{x}
       ++ to the power n, returning 0 when n is out of range.
    qelt: (%, Dom) -> Im
       ++ qelt(u, x) applies \axiom{u} to \axiom{x} without checking whether
       ++ \axiom{x} is in the domain of \axiom{u}.  If \axiom{x} is not in the
       ++ domain of \axiom{u} a memory-access violation may occur.  If a check
       ++ on whether \axiom{x} is in the domain of \axiom{u} is required, use
       ++ the function \axiom{elt}.
    if % has shallowlyMutable then
       set!: (%, Dom, Im) -> Im
       setelt : (%, Dom, Im) -> Im
           ++ setelt(u,x,y) sets the image of x to be y under u,
           ++ assuming x is in the domain of u.
           ++ Error: if x is not in the domain of u.
           -- this function will soon be renamed as setelt!.
       qsetelt!: (%, Dom, Im) -> Im
           ++ qsetelt!(u,x,y) sets the image of \axiom{x} to be \axiom{y} under
           ++ \axiom{u}, without checking that \axiom{x} is in the domain of
           ++ \axiom{u}.
           ++ If such a check is required use the function \axiom{setelt}.
    default
      default a: %
      default x: Dom
      default v: Im
      default y: Im
      qelt(a, x): Im == elt(a, x)
      set!(a, x, v): Im == setelt(a, x, v)
      if % has shallowlyMutable then
        qsetelt!(a, x, y): Im == (a.x := y)
