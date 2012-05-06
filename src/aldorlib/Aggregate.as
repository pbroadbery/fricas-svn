#include "axiom.as"

import from Boolean;

Aggregate: Category == with {
   eq?: (%,%) -> Boolean;
     ++ eq?(u,v) tests if u and v are same objects.
   copy: % -> %;
     ++ copy(u) returns a top-level (non-recursive) copy of u.
     ++ Note: for collections, \axiom{copy(u) == [x for x in u]}.
   empty: () -> %;
     ++ empty()$D creates an aggregate of type D with 0 elements.
     ++ Note: The {\em $D} can be dropped if understood by context,
     ++ e.g. \axiom{u: D := empty()}.
   empty?: % -> Boolean;
     ++ empty?(u) tests if u has 0 elements.
   less?: (%,NonNegativeInteger) -> Boolean;
     ++ less?(u,n) tests if u has less than n elements.
   more?: (%,NonNegativeInteger) -> Boolean;
     ++ more?(u,n) tests if u has greater than n elements.
   size?: (%,NonNegativeInteger) -> Boolean;
     ++ size?(u,n) tests if u has exactly n elements.
   sample: () -> %;    ++ sample yields a value of type %
   if % has finiteAggregate then {
     #: % -> NonNegativeInteger     ++ # u returns the number of items in u.
   }
 default {
  default a, b: %;
  default n: NonNegativeInteger;
  import from XLisp;
  import from NonNegativeInteger;

  eq?(a,b): Boolean == EQ(lisp(%)(a),lisp(%)(b))$XLisp;
  sample(): % == empty();
  if % has finiteAggregate then {
    empty? a: Boolean   == #a = 0;
    less?(a,n): Boolean == #a < n;
    more?(a,n): Boolean == #a > n;
    size?(a,n): Boolean == #a = n;
  }
}
}
