--DEPS: OrderedSet Logic OneDimensionalArrayAggregate init_Boolean
#include "axiom.as"

#pile

BitAggregate: Category ==
  Join(OrderedSet, Logic, OneDimensionalArrayAggregate Boolean) with
    _not: % -> %
      ++ not(b) returns the logical {\em not} of bit aggregate
      ++ \axiom{b}.
    nand : (%, %) -> %
      ++ nand(a,b) returns the logical {\em nand} of bit aggregates \axiom{a}
      ++ and \axiom{b}.
    nor  : (%, %) -> %
      ++ nor(a,b) returns the logical {\em nor} of bit aggregates \axiom{a} and
      ++ \axiom{b}.
    _and : (%, %) -> %
      ++ a and b returns the logical {\em and} of bit aggregates \axiom{a} and
      ++ \axiom{b}.
    _or  : (%, %) -> %
      ++ a or b returns the logical {\em or} of bit aggregates \axiom{a} and
      ++ \axiom{b}.
    xor  : (%, %) -> %
      ++ xor(a,b) returns the logical {\em exclusive-or} of bit aggregates
      ++ \axiom{a} and \axiom{b}.

    default
      default u, v: %
      import from Boolean
      _not v: %      == map(_not, v)
      ~(v): %      == map(_not, v)-- is ~ different to not?
      (/\)(v, u): % == map(/\, v, u)
      (\/)(v, u): % == map(\/, v, u)
      nand(v, u): % == map(nand, v, u)
      nor(v, u): %  == map(nor, v, u)
