--DEPS: SetCategory sexpr/SExpression_SExpressionCategory None
--DEPS: Reference Boolean List
#include "axiom.as"

#pile

import from Boolean
import from System
import from String

Any: SetCategory with
        any            : (SExpression, None) -> %
          ++ any(type,object) is a technical function for creating
          ++ an object of \spadtype{Any}. Arugment \spad{type} is a \spadgloss{LISP} form
          ++ for the type of \spad{object}.
        domainOf        : % -> OutputForm
          ++ domainOf(a) returns a printable form of the type of the
          ++ original object that was converted to \spadtype{Any}.
        objectOf        : % -> OutputForm
          ++ objectOf(a) returns a printable form of the
          ++ original object that was converted to \spadtype{Any}.
        dom             : % -> SExpression
          ++ dom(a) returns a \spadgloss{LISP} form of the type of the
          ++ original object that was converted to \spadtype{Any}.
        obj             : % -> None
          ++ obj(a) essentially returns the original object that was
          ++ converted to \spadtype{Any} except that the type is forced
          ++ to be \spadtype{None}.
        showTypeInOutput: Boolean -> String
          ++ showTypeInOutput(bool) affects the way objects of
          ++ \spadtype{Any} are displayed. If \spad{bool} is true
          ++ then the type of the original object that was converted
          ++ to \spadtype{Any} will be printed. If \spad{bool} is
          ++ false, it will not be printed.

 == add
     Rep == Record(dm: SExpression, ob: None)
     import from Rep
     import from List SExpression;
     import from SExpression;
     import from List Symbol;
     import from Symbol;

     default x, y: %;
     
     import {
         evalType: SExpression -> with;
	 spad2BootCoerce: (None, SExpression, List Symbol) -> OutputForm;
	 devaluate: SExpression -> SExpression;
	 prefix2String: SExpression -> Symbol;
	 isValidType: SExpression -> Boolean
     } from Foreign Lisp;

     printTypeInOutputP: Reference(Boolean) := _ref false

     obj x: None        == rep(x).ob
     dom x: SExpression == rep(x).dm

     domainOf x: OutputForm == rep(x).dm pretend OutputForm

     x = y: Boolean      ==
         dx := dom x
         dy := dom y
         dx ~= dy => false
         Dx : with == evalType(dx)
	 testEq(Dx, x, y);
     
     testEq(Dx: with, x, y): Boolean == 
         if Dx has BasicType then 
	     import from Dx;
             return (obj x) pretend Dx = (obj y) pretend Dx
         -- FIXME: we want
         -- error "Comparison in domain which is not a BasicType"
         -- but currently pattern matching needs
         EQ(obj x, obj y)$ListLisp(None)
     

     objectOf(x : %) : OutputForm ==
       spad2BootCoerce(obj x, dom x,
          list(#"OutputForm")$List(Symbol))

     showTypeInOutput(b : Boolean) : String ==
      free printTypeInOutputP := _ref b
      b => "Type of object will be displayed in output of a member of Any"
      "Type of object will not be displayed in output of a member of Any"

     coerce(x):OutputForm ==
       import from List OutputForm
       obj1 : OutputForm := objectOf x
       not deref printTypeInOutputP => obj1
       dom1 :=
         p:Symbol := prefix2String(devaluate(dom x))
         atom?(p pretend SExpression) => list(p)$List(Symbol)
         list(p)
       hconcat cons(obj1,
         cons(":"::OutputForm, [a::OutputForm for a in dom1]))

     any(domain: SExpression, object: None): % ==
       (isValidType(domain))@Boolean => per [domain, object]
       domain := devaluate(domain)
       (isValidType(domain))@Boolean => per [domain, object]
       error "function any must have a domain as first argument"
