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

# This is a representation for congruence over an fp monoid which use an
# isomorphism to an fp semigroup to perform all computations. 
#
# The components are:
#
#   semicong: the congruence on the isomorphic fp semigroup generated by the
#             images of the generating pairs of the fp monoid congruence. 

DeclareRepresentation(IsFpMonoidCongruenceByIsoToFpSemigroupRep, 
                      IsFpMonoidCongruence,
                      ["semicong"]);

# This is a representation for classes of a congruence in the representation 
# IsFpMonoidCongruenceByIsoToFpSemigroupRep.
#
# The components are:
#
#   semiclass: the class of the congruence semicong from
#              IsFpMonoidCongruenceByIsoToFpSemigroupRep that corresponds to 
#              the class of the fp monoid. 

DeclareRepresentation(IsFpMonoidCongruenceClassByIsoToFpSemigroup, 
                      IsFpMonoidCongruenceClass,
                      ["semiclass"]);
