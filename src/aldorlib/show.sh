#!/bin/bash

base=$1
set -x
$aldor -I$srcdir -Y. -lAxiom=axiom_$* -gloop <<EOF
#include "axiom.as"
#library R "$base.ao"
import from R;
$base
EOF