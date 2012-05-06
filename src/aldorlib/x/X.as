--DEPS: lang
#include "axiom"
#pile

Basic: Category == with
#if 0
Foo(I: Basic): with 
   f: () -> ()
   g: () -> ()
== add
   import from Bar I
   f(): () == a()
   g(): () == never

Bar(I: Basic): with
   a: () -> ()
== add
   import from Foo I
   a(): () == g()

#endif

--#if 0
Foo(): with 
   f: () -> ()
   g: () -> ()
== add
   import from Bar()
   f(): () == a()
   g(): () == never

Bar(): with
   a: () -> ()
== add
   import from Foo()
   a(): () == g()
--#endif

#if 0
Foo: with 
   f: () -> ()
   g: () -> ()
== add
   import from Bar
   f(): () == a()
   g(): () == never

Bar: with
   a: () -> ()
== add
   import from Foo
   a(): () == g()
#endif