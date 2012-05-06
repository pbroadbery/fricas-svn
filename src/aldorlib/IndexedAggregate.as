--DEPS:  EltableAggregate OrderedSet Void HomogeneousAggregate finiteAggregate
#include "axiom.as"

import from Boolean;

IndexedAggregate(Index: SetCategory, Entry: Type): Category == 
  Join(HomogeneousAggregate(Entry), EltableAggregate(Index, Entry)) with {
   entries: % -> List Entry;
      ++ entries(u) returns a list of all the entries of aggregate u
      ++ in no assumed order.
      -- to become entries: % -> Entry* and entries: % -> Iterator(Entry,Entry)
   index?: (Index,%) -> Boolean;
      ++ index?(i,u) tests if i is an index of aggregate u.
   indices: % -> List Index;
      ++ indices(u) returns a list of indices of aggregate u in no
      ++ particular order.
      -- to become indices: % -> Index* and indices: % -> Iterator(Index,Index).
-- map: ((Entry,Entry)->Entry,%,%,Entry) -> %
--    ++ exists c = map(f,a,b,x), i:Index where
--    ++    c.i = f(a(i,x),b(i,x)) | index?(i,a) or index?(i,b)
   if Entry has SetCategory and % has finiteAggregate then {
      entry?: (Entry,%) -> Boolean;
        ++ entry?(x,u) tests if x equals \axiom{u . i} for some index i.
   }
   if Index has OrderedSet then {
      maxIndex: % -> Index;
        ++ maxIndex(u) returns the maximum index i of aggregate u.
        ++ Note: in general,
        ++ \axiom{maxIndex(u) = reduce(max,[i for i in indices u])};
        ++ if u is a list, \axiom{maxIndex(u) = #u}.
      minIndex: % -> Index;
        ++ minIndex(u) returns the minimum index i of aggregate u.
        ++ Note: in general,
        ++ \axiom{minIndex(a) = reduce(min,[i for i in indices a])};
        ++ for lists, \axiom{minIndex(a) = 1}.
      first   : % -> Entry;
        ++ first(u) returns the first element x of u.
        ++ Note: for collections, \axiom{first([x,y,...,z]) = x}.
        ++ Error: if u is empty.
   }
   if % has shallowlyMutable then {
      fill!: (%,Entry) -> %;
        ++ fill!(u,x) replaces each entry in aggregate u by x.
        ++ The modified u is returned as value.
      swap!: (%,Index,Index) -> ();
        ++ swap!(u,i,j) interchanges elements i and j of aggregate u.
        ++ No meaningful value is returned.
   }
 default {
  default a: %;
  default i,j: Index;
  default x: Entry;
  elt(a, i, x): Entry == (index?(i, a) => qelt(a, i); x);

  if % has finiteAggregate then {
    entries a: List Entry == parts a;
    if Entry has SetCategory then
      entry?(x, a): Boolean == member?(x, a)
  }
  if Index has OrderedSet then {
    import from Index;
    import from Fold Index;
    maxIndex a: Index == max/indices(a);
    minIndex a: Index == min/indices(a);
    first a: Entry  == a minIndex a;
  }
  if % has shallowlyMutable then {
    import from List Index;
    E ==> Entry;
    map(f: E-> E, a): % == map!(f, copy a);

    map!(f: E->E, a): % == {
      for i in indices a repeat qsetelt!(a, i, f qelt(a, i));
      a}

    fill!(a, x): % == {
      for i in indices a repeat qsetelt!(a, i, x);
      a}

    swap!(a, i, j): () == {
      t := a.i;
      qsetelt!(a, i, a.j);
      qsetelt!(a, j, t);}
}
}
}