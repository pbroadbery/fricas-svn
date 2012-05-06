--DEPS: IndexedDirectProductCategory List OutputForm
#include "axiom.as"

#pile
import from Boolean;
import from System;
import from String;

IndexedDirectProductObject(A : SetCategory, S : OrderedSet
                          ) : IndexedDirectProductCategory(A, S) with _
 == add 
    --representations
       Term ==>  Record(k:S,c:A);
       Rep ==  List Term;
       import from Rep;
       import from Term;
    --declarations
       default x,y: %;
       default f: A -> A;
       default s: S;
       default r: A;
       default lx : List Term;

       local null(x: %): Boolean == null rep(x)
       local empty?(x: %): Boolean == null rep(x)
       local apply(x: %, zz: 'first'): Term == rep(x).first
       local apply(x: %, zz: 'rest'): % == per(rep(x).rest)

    --define
       x = y: Boolean  == 
         while not null x and not null y repeat 
           x.first.k ~= y.first.k => return false;
           x.first.c ~= y.first.c => return false;
           x:=x.rest;
           y:=y.rest;
         null x and null y

       coerce(x:%):OutputForm == 
          import from List OutputForm
          bracket [rarrow(t.k :: OutputForm, t.c :: OutputForm) for t in x]

       -- sample():% == [[sample()$S,sample()$A]$Term]$Rep

       SMALLER__DEF(cmp__x__0, cmp__0__y) ==>
           smaller?(x : %, y : %) : Boolean ==
               repeat
                   null(y) =>
                       null(x) => return false
                       return cmp__x__0
                   null(x) => return cmp__0__y
                   if x.first.k = y.first.k then
                       if x.first.c = y.first.c then
                           x := x.rest
                           y := y.rest
                       else
                           return smaller?(x.first.c, y.first.c)
                   else
                       x.first.k < y.first.k => return cmp__0__y
                       return cmp__x__0

       if A has AbelianMonoid then 

           monomial(r,s): % == (r = 0 => 0; per [[s,r]]);
           map(f,x): % == per [[tm.k,a] for tm in rep(x) | not((a:=f(tm.c)) = 0$A)];

           reductum x: %     == (null x => 0; x.rest);
           leadingCoefficient x: A  == (null x => 0; x.first.c);
           if A has Comparable then 
               SMALLER__DEF(smaller?(x.first.c, 0$A),
                            smaller?(0$A, y.first.c))
               
           
       
       else
           monomial(r,s): % == per [[s,r]];
           map(f,x): % == per [[tm.k,f(tm.c)] for tm in rep(x)];

           reductum x: %     == x.rest;
           leadingCoefficient x: A  ==
               null x =>
                   error "Can't take leadingCoefficient of empty product element";
               x.first.c
           if A has Comparable then 
               SMALLER__DEF(false, true)
          
       leadingSupport x: S  == 
          null x => error "Can't take leadingCoefficient of empty product element";
          x.first.k

       -- ordering of terms
       local compareterm:(Term,Term) -> Boolean;

       compareterm(a:Term,b:Term):Boolean == 
          a.k > b.k;

       construct(lx): % ==
          per sort(compareterm, lx);

       constructOrdered(lx): % == per lx;

       leadingTerm x: Term == 
          null x => error "Can't take leadingCoefficient of empty product element";
          x.first

       listOfTerms x: List Term == rep x
       generator x: Generator Term == generator rep x
       bracket(g: Generator Term): % == per [g]

       local qsetrest!(xx: Rep, newcell: Rep): () == xx.rest := newcell

--       TermS ==>  Record(k : SingleInteger, c : A);
--       RepS ==> List TermS;
--       import from TermS;

       PLUS__BODY ==>
                endcell := empty()
                res := empty()
                while not empty? __x and not empty? __y repeat
                        newcell := empty()
                        if __x.first.k = __y.first.k then
                                r:= __x.first.c + __y.first.c
                                if not zero? r then
                                        newcell := cons([__x.first.k, r], empty())
                                __x := rest __x
                                __y := rest __y
                        else if __y.first.k < __x.first.k then
                                newcell := cons(__x.first, empty())
                                __x := rest __x
                        else
                                newcell := cons(__y.first, empty())
                                __y := rest __y
                        if not empty? newcell then
                                if not empty? endcell then
                                        qsetrest!(endcell, newcell)
                                        endcell := newcell
                                else
                                        res     := newcell
                                        endcell := res
                if empty? __x then end := __y
                else end := __x
                if empty? res then res := end
                else qsetrest!(endcell, end)
                res

       if A has AbelianMonoid then

           0: %  == per []
           zero? x: Boolean ==  null x

           add__gen(__x : Rep, __y : Rep) : Rep ==
               null __x => __y
               null __y => __x
               local endcell : Rep
               local res :  Rep
               local newcell : Rep
               PLUS__BODY

           x + y: % == per add__gen(rep x, rep y)

--         if S is NonNegativeInteger then
--               add__si(__x : RepS, __y : RepS) : RepS ==
--                   local endcell : RepS
--                   local res :  RepS
--                   local newcell : RepS
--                   PLUS__BODY

--               x + y: % ==
--                   null x => y
--                   null y => x
--                   degx := (x.first.k) pretend Integer
--                   degy := (y.first.k) pretend Integer
--                   msi := max()$SingleInteger
--                   degx < msi and degy < msi =>
--                       return add__si(x pretend RepS, y pretend RepS) pretend %
--                   add__gen(x, y)
--
--           else
--               x + y: % == add__gen(x, y)

           (n: Integer) * (x: %): %  ==
               import from NonNegativeInteger
               n = 0 => 0
               n = 1 => x
               per [[u.k,a] for u in rep(x) | (a:=n::NonNegativeInteger*u.c) ~= 0$A]

       if A has AbelianGroup then
           -x: % == per [[u.k,-u.c] for u in rep(x)]
           (n : Integer) * (x : %): %  ==
                 n = 0 => 0
                 n = 1 => x
                 per [[u.k,a] for u in rep(x) | (a:=n*u.c) ~= 0$A]


           x - y: % ==
               null x => -y
               null y => x
               endcell: Rep := empty()
               res:  Rep := empty()
               while not empty? x and not empty? y repeat
                   newcell := empty()
                   if x.first.k = y.first.k then
                       r := x.first.c - y.first.c
                       if not zero? r then
                           newcell := cons([x.first.k, r], empty())
                       x := x.rest
                       y := y.rest
                   else if y.first.k < x.first.k then
                       newcell := cons(x.first, empty())
                       x := x.rest
                   else
                       newcell := cons([y.first.k, -y.first.c], empty())
                       y := y.rest
                   if not empty? newcell then
                       if not empty? endcell then
                           qsetrest!(endcell, newcell)
                           endcell := newcell
                       else
                           res := newcell
                           endcell := res
               if empty? x then end := - y
               else end := x
               if empty? res then res := rep(end)
               else qsetrest!(endcell, rep(end))
               per res

       if A has CancellationAbelianMonoid then
           subtractIfCan(x, y): Partial % ==
               import from Partial A
               null y => success(x)
               endcell: Rep := empty()
               res:  Rep := empty()
               while not empty? x and not empty? y repeat
                   newcell := empty()
                   if x.first.k = y.first.k then
                       ru := subtractIfCan(x.first.c, y.first.c)
                       failed? ru => return failed()
                       r := ru::A
                       if not zero? r then
                           newcell := cons([x.first.k, r], empty())
                       x := x.rest
                       y := y.rest
                   else if x.first.k > y.first.k then
                       newcell := cons(x.first, empty())
                       x := x.rest
                   else
                       ru := subtractIfCan(0$A, y.first.c)
                       failed? ru => return failed()
                       r := ru::A
                       newcell := cons([y.first.k, r], empty())
                       y := y.rest
                   if not empty? newcell then
                       if not empty? endcell then
                           qsetrest!(endcell, newcell)
                           endcell := newcell
                       else
                           res := newcell
                           endcell := res
               empty? x =>
                   while not empty? y repeat
                       ru := subtractIfCan(0$A, y.first.c)
                       failed? ru => return failed()
                       r := ru::A
                       newcell := cons([y.first.k, r], empty())
                       y := y.rest
                       if not empty? endcell then
                           qsetrest!(endcell, newcell)
                           endcell := newcell
                       else
                           res     := newcell
                           endcell := res
                   success(per res)
               if empty? res then res := rep x
               else qsetrest!(endcell, rep x)
               success(per res)

       if A has OrderedAbelianMonoid then

           x < y: Boolean == smaller?(x, y)

       if A has OrderedAbelianMonoidSup then

           sup(x, y): % ==
               empty? y => x
               empty? x => y
               x.first.k < y.first.k => per cons(y.first, rep sup(x, y.rest))
               x.first.k > y.first.k => per cons(x.first, rep sup(x.rest, y))
               u := sup(x.first.c, y.first.c)
               per cons([x.first.k, u], rep sup(x.rest, y.rest))

