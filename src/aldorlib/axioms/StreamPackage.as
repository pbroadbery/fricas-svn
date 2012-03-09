--DEPS: lang init_Generator Tuple
#include "axiom.as"

StreamPackage: with 
   pair: (T: Type) -> Stream T -> Stream Cross(T, T)
== add {
   pair(T: Type)(f: Stream T): Stream(T, T) == [(a, b) for a in f for b in f]
   allpairs(T: Type)(f: Stream T): Stream(T, T) == for i in f for strm in reverseSegments 

}


allPairs(s: Stream T): Stream Cross(e1, e2) == generate {
   for i in 1.. repeat for e1 in first(i, s) for e2 in reverseFirst(i, s) repeat yield (e1, e2)
}

local reverseFirst(i: Integer, s: Stream t): Stream T == {
     l := empty();
     for e in s for j in 1..i repeat l := cons(e, l)
     for e in l repeat yield e;
}

local first(i: Integer, s: Stream t): Stream T == {
     l := empty();
     for e in s for j in 1..i repeat yield e
}
