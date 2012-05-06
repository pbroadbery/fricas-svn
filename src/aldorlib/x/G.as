--DEPS: lang init_Generator
#include "axiom.as"

SeqCategory(T: with): Category == with {
   generator: % -> Generator T;
   generator: % -> Generator Cross(T, T);
   value: () -> %;
} 

foo1(T1: with, T2: with, S1: SeqCategory T1, S2: SeqCategory T2): () == {
   import from S1;
   import from S2;
   v1: S1 := value();
   v2: S2 := value();
   default x: T1;
   x for x in v1;
   never
}

foo2(T1: with, T2: with, S1: SeqCategory T1, S2: SeqCategory T2): () == {
   import from S1;
   import from S2;
   local x: T1;
   for free x in value() repeat {
      x
   }
   never
}

#if 0
foo2(T1: with, T2: with, S1: SeqCategory T1, S2: SeqCategory T2): () == {
   import from S1;
   import from S2;
   local x: T1;
   local y: T1;
   for (free x, free y) in value() repeat {
      x
   }
   never
}

#endif
