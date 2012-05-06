--DEPS: PolynomialCategory UserDefinedPartialOrdering SparseMultivariatePolynomial

#include "axiom.as"

#pile
import from Boolean

Polynomial(R:Ring):
  PolynomialCategory(R, IndexedExponents Symbol, Symbol) with
   if R has Algebra Fraction Integer then
     integrate: (%, Symbol) -> %
       ++ integrate(p,x) computes the integral of \spad{p*dx}, i.e.
       ++ integrates the polynomial p with respect to the variable x.
 == SparseMultivariatePolynomial(R, Symbol) add

    import from UserDefinedPartialOrdering(Symbol)

    coerce(p:%):OutputForm ==
      success?(r:= retractIfCan(p)) => r::R::OutputForm
      a :=
        userOrdered?() => largest variables p
        mainVariable(p)::Symbol
      outputForm(univariate(p, a), a::OutputForm)

    if R has Algebra Fraction Integer then
      integrate(p: %, x: Symbol): % == (integrate univariate(p, x)) (x::%)
