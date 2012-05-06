--DEPS: EuclideanDomain0 PrincipalIdealDomain
#include "axiom.as"

import from Boolean;

EuclideanDomain: Category == Join(EuclideanDomain0, PrincipalIdealDomain)