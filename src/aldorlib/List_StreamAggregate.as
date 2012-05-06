--DEPS: List StreamAggregate

#include "axiom.as"

extend List(T: Type): StreamAggregate T with {
}
== add {
	copy(x: %): % == never;
	leaves(l: %): List(T) == never;
	distance(x: %, y: %): Integer == never;
	first(l: %, n: NonNegativeInteger): % == never;
	constructList(t: T): % == never;
	new(n: NonNegativeInteger, t: T): % == never;
	map(f: (T, T)-> T, l1: %, l2: %): % == never;
	delete(l: %, n: Integer): % == never;
	delete(l: %, r: UniversalSegment(Integer)): % == never;
	insert(l1: %, l2: %, n: Integer): % == never;
	construct(l: List T): % == l;
}