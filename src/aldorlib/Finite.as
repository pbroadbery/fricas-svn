--DEPS: NonNegativeInteger SetCategory ConvertibleTo init_InputForm
--DEPS: init_PositiveInteger List_StreamAggregate Integer_OrderedRing

#include "axiom.as"

import from Boolean;

Finite: Category == Join(SetCategory, ConvertibleTo InputForm) with {
    --operations
      size: () ->  NonNegativeInteger;
        ++ size() returns the number of elements in the set.
      index: PositiveInteger -> %;
        ++ index(i) takes a positive integer i less than or equal
        ++ to \spad{size()} and
        ++ returns the \spad{i}-th element of the set. This operation establishs a bijection
        ++ between the elements of the finite set and \spad{1..size()}.
      lookup: % -> PositiveInteger;
        ++ lookup(x) returns a positive integer such that
        ++ \spad{x = index lookup x}.
      random: () -> %;
        ++ random() returns a random element from the set.
      enumerate: () -> List %;
        ++ enumerate() returns list of elements of the set.
  default {
      import from NonNegativeInteger;
      import from PositiveInteger;
      import from UniversalSegment Integer;
      import from List %;
      import from Integer;

      random(): % == index((1+random(size()$%))::PositiveInteger);

      enumerate(): List % == [index(i::PositiveInteger) for i in 1..size()::Integer];

      convert(x: %): InputForm == never;
}
}