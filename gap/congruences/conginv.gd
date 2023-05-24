############################################################################
##
##  congruences/conginv.gd
##  Copyright (C) 2015-2022                               Michael C. Young
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
## This file contains methods for congruences on inverse semigroups, using the
## "kernel and trace" representation - see Howie 5.3
##

# Inverse Congruences By Kernel and Trace
DeclareCategory("IsInverseSemigroupCongruenceByKernelTrace",
                IsSemigroupCongruence
                and IsMagmaCongruence
                and CanComputeEquivalenceRelationPartition
                and IsAttributeStoringRep
                and IsFinite);
DeclareGlobalFunction("InverseSemigroupCongruenceByKernelTrace");
DeclareGlobalFunction("InverseSemigroupCongruenceByKernelTraceNC");

DeclareAttribute("TraceOfSemigroupCongruence", IsSemigroupCongruence);
DeclareAttribute("KernelOfSemigroupCongruence", IsSemigroupCongruence);
DeclareAttribute("AsInverseSemigroupCongruenceByKernelTrace",
                 IsSemigroupCongruence);
DeclareAttribute("InverseSemigroupCongruenceClassByKernelTraceType",
                 IsInverseSemigroupCongruenceByKernelTrace);

# Congruence Classes
DeclareCategory("IsInverseSemigroupCongruenceClassByKernelTrace",
                IsCongruenceClass and IsAttributeStoringRep and
                IsMultiplicativeElement);

# Special congruences
DeclareAttribute("MinimumGroupCongruence",
                 IsInverseSemigroup and IsGeneratorsOfInverseSemigroup);
DeclareAttribute("MaximumIdempotentSeparatingCongruence",
                 IsInverseSemigroup and IsGeneratorsOfInverseSemigroup);

DeclareProperty("IsIdempotentPureCongruence", IsSemigroupCongruence);

DeclareOperation("IsNormalCongruence",
                 [IsInverseSemigroup, IsSemigroupCongruence]);

# Normal congruence of semilattice of idempotents
DeclareAttribute("PrincipalNormalCongruencesIdempotentSemilattice",
                 IsInverseSemigroup);
DeclareAttribute("NormalCongruencesIdempotentSemilattice", IsInverseSemigroup);

DeclareAttribute("PrincipalIdempotentPureCongruences",
                 IsInverseSemigroup);
DeclareAttribute("IdempotentPureCongruences", IsInverseSemigroup);

DeclareAttribute("SyntacticCongruence", IsInverseSemigroup);

DeclareAttribute("InverseSemigroupQuotientData",
                 IsInverseSemigroupCongruenceByKernelTrace);



