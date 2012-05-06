#!/bin/bash

base=$1
set -x

cat > /var/tmp/$$.as <<EOF
#include "axiom.as"
import from Axiom;
import from Boolean;
EOF

(cat /var/tmp/$$.as ; cat) | $aldor -I$srcdir -Y. -lAxiom=axiom_$* -gloop 
