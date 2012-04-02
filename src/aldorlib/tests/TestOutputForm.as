--DEPS: List OutputForm runtime/ARCH/rtexns tests/TestCategory
#include "axiom.as"

import from OutputForm;
import from String;

TestOutputForm: TestCategory 
== add {
test(): () == {
       import from IO;
       import from List Integer;
       import from List OutputForm;
       import from OutputForm;
       import from Integer;
       import from SExpression;
       
       print outputForm 123;
       print outputForm "done";
       print outputForm unparse(outputForm "done" pretend SExpression);
       print [outputForm "hello"];
       o: OutputForm := [outputForm "hello"] ;
       print unparse(o pretend SExpression);
       q: SExpression := o pretend SExpression;
       
       print outputForm unparse q;
       print outputForm unparse cdr q;
}


assertTrue(x: Boolean): () == if not x then never;

assertEqual(s1: SExpression, s2: SExpression): () == {
       if not(s1 = s2) then 
            print concat("Not equal: ", concat(unparse s1, concat(",", unparse s2)));
}

}