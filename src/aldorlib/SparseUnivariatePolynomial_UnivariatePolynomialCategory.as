--DEPS:SparseUnivariatePolynomial_R UnivariatePolynomialCategory Integer_SetCategory
#include "axiom.as"
#pile

extend SparseUnivariatePolynomial(R: Ring): UnivariatePolynomialCategory R with 
     outputForm : (%,OutputForm) -> OutputForm
        ++ outputForm(p,var) converts the SparseUnivariatePolynomial p to
        ++ an output form (see \spadtype{OutputForm}) printed as a polynomial in the
        ++ output form variable.
== add
   Term ==>  Record(k:NonNegativeInteger,c:R)
   Rep ==  List Term
   import from Term, Rep
   import from Integer;

   local listOfTerms(x: %): List Term == rep(x)

   local generator(p: %): Generator Term == x for x in listOfTerms p

   outputForm(p:%, v:OutputForm): OutputForm ==
     local l: List(OutputForm)
     l:=[toutput(t,v) for t in p]
     null l => (0$Integer)::OutputForm -- else FreeModule 0 problems
     reduce(+,l)

   toutput(t1:Term,v:OutputForm):OutputForm ==
     t1.k = 0 => t1.c :: OutputForm
     if t1.k = 1
       then mon:= v
       else mon := v ^ t1.k::OutputForm
     t1.c = 1 => mon
     t1.c = -1 and
          ((t1.c :: OutputForm) = (-1$Integer)::OutputForm)@Boolean => - mon
     t1.c::OutputForm * mon
