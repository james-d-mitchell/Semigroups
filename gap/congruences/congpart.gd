############################################################################
##
##  congruences/congpart.gd
##  Copyright (C) 2022                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
############################################################################
##
## This file contains declarations for left, right, and two-sided congruences
## that can compute EquivalenceRelationPartition.

# TODO(now)
# Provide default implementations of the following:
# * EquivalenceClasses
# * ImagesElm (for the calculation of the elements of an equivalence class)
# * NrEquivalenceClasses (this could be computed from EquivalenceClasses, but
#   usually there's a lower cost way of counting the number)
# * CongruenceTestMembershipNC

###############################################################################
###############################################################################
# The following are the fundamental attributes for a congruence in
# CanComputeEquivalenceRelationPartition.  If defining a new type of congruence
# in this representation it is necessary to provide methods for the following:
#
# * EquivalenceRelationPartition
#
# and then the following attributes can be computed (by default, if no better
# method is known) from the EquivalenceRelationPartition:
#
# *
#
# TODO dependency diagram
#
# If a congruence <C> knows its generating pairs, knows its source/range,
# CanUseFroidurePin(Range(C)) is true, and HasGeneratorsOfSemigroup(Range(C))
# is true, then <C> automatically satisfies CanUseLibsemigroupsCongruence, and
# the generating pairs are used to construct a libsemigroups Congruence object
# representing <C>, and this object will be used to perform many computations
# for <C>. If you never want to construct such a libsemigroups Congruence
# object representing for <C>, then an immediate method should be installed in
# libsemigroups/cong.gi explicitly excluding this type of congruence, and the
# following methods must be implemented for the new type of congruences:
#
# *
#
# To define a new type of congruence that does not implement any of the above
# (i.e. that uses libsemigroups Congruence objects to compute
# EquivalenceRelationPartition), it's sufficient to ensure that the
# congruence's generating pairs are computed in the function where it is
# Objectified.
#
# There are some types of congruences in the Semigroups package which use both
# a specialised representation for some things, and use a libsemigroups
# Congruence object for others:
#
# * IsCongruenceByWangPair;
#
# there are others that never use libsemigroups Congruence objects:
#
# * IsInverseSemigroupCongruenceByKernelTrace;
# * IsSimpleSemigroupCongruence;
# * IsReesCongruence;
# * IsRMSCongruenceByLinkedTriple;
# * IsUniversalSemigroupCongruence;
#
# and some that always do (congruences defined by generating pairs, not
# belonging to the previous types).
#
###############################################################################
###############################################################################

DeclareProperty("CanComputeEquivalenceRelationPartition",
                IsLeftRightOrTwoSidedCongruence);

