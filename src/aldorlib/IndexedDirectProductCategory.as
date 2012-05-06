--DEPS: SetCategory OrderedSet AbelianProductCategory Comparable
--DEPS: OrderedAbelianMonoidSup init_Generator List

#include "axiom.as"
import from Boolean;

IndexedDirectProductCategory(A : SetCategory, S : OrderedSet) : Category
 == AbelianProductCategory(A) with {
      Term ==> Record(k:S,c:A);


      if A has Comparable then Comparable;
      if A has OrderedAbelianMonoid then OrderedAbelianMonoid;
      if A has OrderedAbelianMonoidSup then OrderedAbelianMonoidSup;

      map:           (A -> A, %) -> %;
         ++ map(f,z) returns the new element created by applying the
         ++ function f to each component of the direct product element z.
      monomial:         (A, S) -> %;
         ++ monomial(a,s) constructs a direct product element with the s
         ++ component set to \spad{a}
      leadingCoefficient:   % -> A;
         ++ leadingCoefficient(z) returns the coefficient of the leading
         ++ (with respect to the ordering on the indexing set)
         ++ monomial of z.
         ++ Error: if z has no support.
      leadingSupport:   % -> S;
         ++ leadingSupport(z) returns the index of leading
         ++ (with respect to the ordering on the indexing set) monomial of z.
         ++ Error: if z has no support.
      reductum:      % -> %;
         ++ \spad{reductum(z)} returns a new element created by removing the
         ++ leading coefficient/support pair from the element z.
         ++ Error: if z has no support.
      construct: List Term -> %;
         ++ \spad{construct(l)} takes a list of terms and creates
         ++ the object with these components.
      constructOrdered: List Term -> %;
         ++ \spad{constructOrdered(l)} takes a list of terms and creates
         ++ the object with these components.
         ++ The list is assumed to be sorted (in reverse order) with respect
         ++ to the ordering of S and no checking is performed.
         ++ Caution: This should only be used in cases where
         ++ this condition is assured. If in doubt use construct
      leadingTerm: % -> Term;
         ++ \spad{leadingTerm(x)} returns the leading
         ++ (with respect to the ordering on the indexing set) term of z.
         ++ Error: if z has no support.
      listOfTerms: % -> List Term;
          ++ \spad{listOfTerms(x)} returns a list \spad{lt} of terms with type
          ++ \spad{Record(k: S, c: R)} such that \spad{x} equals
          ++ \spad{constructOrdered lt}.
      generator: % -> Generator Term;
      bracket: Generator Term -> %;
}

