############################################################################
##
#W  congruences/congfpmon.gd
#Y  Copyright (C) 2017                                   Michael C. Torpey
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
## This file contains methods for congruences (left, right, or 2-sided) defined
## by generating pairs on finitely presented monoids.  The approach is, on
## creation, to take an isomorphism to an fp semigroup, and then to call the
## standard methods defined in congpairs.gd/gi to answer any questions about the
## congruence.
##

DeclareCategory("IsFpMonoidCongruence",
                IsEquivalenceRelation and IsAttributeStoringRep,
                RankFilter(IsSemigroupCongruence));

DeclareCategory("IsFpMonoidCongruenceClass",
                IsEquivalenceClass and IsAttributeStoringRep and
                IsAssociativeElement,
                RankFilter(IsCongruenceClass));
