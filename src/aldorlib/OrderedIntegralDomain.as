--DEPS:  OrderedRing IntegralDomain
#include "axiom"

import from Boolean;

OrderedIntegralDomain: Category == Join(IntegralDomain, OrderedRing) with;
