--DEPS: SetCategory Boolean String OutputForm
#include "axiom.as"

#pile

import from Boolean
import from String

Reference(S:Type): with 
        _ref   : S -> %
          ++  ref(n) creates a pointer (reference) to the object n.
        elt   : % -> S
          ++ elt(n) returns the object n.
        setelt: (%, S) -> S
          ++ setelt(n,m) changes the value of the object n to m.
        -- alternates for when bugs don't allow the above
        deref : % -> S
          ++ deref(n) is equivalent to \spad{elt(n)}.
        setref: (%, S) -> S
          ++ setref(n,m) same as \spad{setelt(n,m)}.
        (=): (%, %) -> Boolean
          ++ a=b tests if \spad{a} and b are equal.
        if S has SetCategory then SetCategory

== add
	default p,q: %
	default v: S

        Rep == Record(value: S)
	import from Rep
	local apply(p: %, xx: 'value'): S == rep(p).value
	local set!(p: %, xx: 'value', s: S): S == rep(p).value := s

	import from Machine

        p = q: Boolean   == ((p pretend Ptr) = (q pretend Ptr)) pretend Boolean
        _ref v: %        == per [v]
        elt p: S        == p.value
        setelt(p, v): S == p.value := v
        deref p: S      == p.value
        setref(p, v): S == p.value := v

	import from List OutputForm
        if S has SetCategory then
          coerce p: OutputForm ==
            prefix(message("ref"@String), [p.value::OutputForm])

