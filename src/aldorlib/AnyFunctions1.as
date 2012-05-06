--DEPS: Any NoneFunctions1
#include "axiom.as"
#pile
import from String;
import from System;

AnyFunctions1(S:Type): with
        coerce      : S -> Any
          ++ coerce(s) creates an object of \spadtype{Any} from the
          ++ object \spad{s} of type \spad{S}.
        retractIfCan: Any -> Partial(S)
          ++ retractIfCan(a) tries change \spad{a} into an object
          ++ of type \spad{S}. If it can, then such an object is
          ++ returned. Otherwise, "failed" is returned.
        retractable?: Any -> Boolean
          ++ retractable?(a) tests if \spad{a} can be converted
          ++ into an object of type \spad{S}.
        retract     : Any -> S
          ++ retract(a) tries to convert \spad{a} into an object of
          ++ type \spad{S}. If possible, it returns the object.
          ++ Error: if no such retraction is possible.

    == add
        import from NoneFunctions1(S)
	default a: Any
	
	import 
	       devaluate: Type -> SExpression
	from Foreign Lisp

        Sexpr:SExpression := devaluate(S)

        retractable? a: Boolean  == dom(a) = Sexpr
        coerce(s:S):Any == any(Sexpr, s::None)

        retractIfCan a: Partial S ==
            retractable? a => [obj(a) pretend S]
            [failed]

        retract a: S ==
            retractable? a => obj(a) pretend S
            error "Cannot retract value."

