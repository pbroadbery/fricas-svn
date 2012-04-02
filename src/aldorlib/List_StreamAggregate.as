--DEPS: List StreamAggregate OutputForm

#include "axiom.as"

local xyzzy: with == add { foo(): List OutputForm == never; }

extend List(T: Type): StreamAggregate T with {
       shallowlyMutable;
       finiteAggregate;
}
== add {
   --- BUG! Cascaded exports should cascade into extensions
        import from 'first', 'rest';

	leaves(l: %): List(T) == never;
	distance(x: %, y: %): Integer == never;
	first(l: %, n: NonNegativeInteger): % == never;
	constructList(t: T): % == never;
	new(n: NonNegativeInteger, t: T): % == never;

	map(f: (T, T)-> T, l1: %, l2: %): % == never;

	delete(l: %, n: Integer): % == never;
	delete(l: %, r: UniversalSegment(Integer)): % == never;

	insert(toInsert: %, insertTarget: %, n: Integer): % == {
	   empty? toInsert => insertTarget;
	   n = 1 => concat(toInsert, insertTarget);
	   cons(first insertTarget, insert(toInsert, rest insertTarget, n - 1))
	}

	construct(l: List T): % == l;

	setfirst!(x: %, t: T): T == {
            x.first := t;
	    t
	}

	setrest!(x: %, y: %): % == {
            x.rest := y;
	    y
	}
	concat!(x: %, t: T): % == {
	    empty? x => cons(t, empty());
	    last := lastCell x;
	    setrest!(x, cons(t, empty()));
	    x
	}
}
