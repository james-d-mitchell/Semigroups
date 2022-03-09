############################################################################
##
##  congruences/cong.gd
##  Copyright (C) 2015-2022                               Michael C. Young
##
##  Licensing information can be found in the README file of this package.
##
############################################################################
##
## This file contains declarations for functions, operations and attributes of
## semigroup congruences.  Methods for most of these are implemented for
## specific types of congruence in the following files:
##
##       conginv.gi     - Inverse semigroups
##       congpairs.gi   - Congruences with generating pairs
##       congrees.gi    - Rees congruences
##       congrms.gi     - (0-)simple Rees matrix semigroups
##       congsimple.gi  - (0-)simple semigroups
##       conguniv.gi    - Universal congruences
##
## Some general functions are also implemented in cong.gi
##

############################################################################
# IsLeft/Right/SemigroupCongruence is a property, but
# IsLeft/Right/MagmaCongruence is a category so we use them in conjunction to
# mean i.e. a left congruence on a semigroup that was created in the category
# of left congruences. We introduce synonyms for these to simplify their use.
#
# Note that IsMagmaCongruence implies IsLeftMagmaCongruence and
# IsRightMagmaCongruence, and so IsLeftCongruenceCategory returns true when
# applied to a 2-sided congruence.
############################################################################

DeclareSynonym("IsLeftCongruenceCategory",
                IsLeftSemigroupCongruence and IsLeftMagmaCongruence);
DeclareSynonym("IsRightCongruenceCategory",
                IsRightSemigroupCongruence and IsRightMagmaCongruence);
DeclareSynonym("IsCongruenceCategory",
                IsSemigroupCongruence and IsMagmaCongruence);

DeclareProperty("IsLeftRightOrTwoSidedCongruence",
                IsLeftCongruenceCategory);
DeclareProperty("IsLeftRightOrTwoSidedCongruence",
                IsRightCongruenceCategory);
DeclareProperty("IsLeftRightOrTwoSidedCongruence",
                IsCongruenceCategory);

InstallTrueMethod(IsLeftRightOrTwoSidedCongruence,
                  IsLeftMagmaCongruence and IsLeftSemigroupCongruence);
InstallTrueMethod(IsLeftRightOrTwoSidedCongruence,
                  IsRightMagmaCongruence and IsRightSemigroupCongruence);
InstallTrueMethod(IsLeftRightOrTwoSidedCongruence,
                  IsMagmaCongruence and IsSemigroupCongruence);

# The next attributes allows us to recover the category/string from a
# left/right/2-sided congruence object
DeclareAttribute("CongruenceCategory",
                 IsLeftRightOrTwoSidedCongruence);
DeclareAttribute("CongruenceCategoryString",
                 IsLeftRightOrTwoSidedCongruence);

############################################################################
# We introduce the property IsLeftRightOrTwoSidedCongruenceClass in a similar
# vein to IsLeftRightOrTwoSidedCongruence. Since we declare
# IsLeftCongruenceClass and IsRightCongruenceClass we could define them to
# satisfy IsLeftRightOrTwoSidedCongruenceClass, but then we have to declare
# IsLeftRightOrTwoSidedCongruenceClass as a being a property of
# IsEquivalenceClass, which means we then have to fiddle with ranks of methods.
############################################################################

# IsCongruenceClass is declared in gap/lib/mgmcong.gd:140
# but it does not include IsAttributeStoringRep
DeclareCategory("IsLeftCongruenceClass",
                IsEquivalenceClass and IsAttributeStoringRep);
DeclareCategory("IsRightCongruenceClass",
                IsEquivalenceClass and IsAttributeStoringRep);

DeclareProperty("IsLeftRightOrTwoSidedCongruenceClass",
                IsLeftCongruenceClass);
DeclareProperty("IsLeftRightOrTwoSidedCongruenceClass",
                IsRightCongruenceClass);
DeclareProperty("IsLeftRightOrTwoSidedCongruenceClass",
                IsCongruenceClass);

InstallTrueMethod(IsLeftRightOrTwoSidedCongruenceClass,
                  IsLeftCongruenceClass);
InstallTrueMethod(IsLeftRightOrTwoSidedCongruenceClass,
                  IsRightCongruenceClass);
InstallTrueMethod(IsLeftRightOrTwoSidedCongruenceClass,
                  IsCongruenceClass);

########################################################################
# Congruences
########################################################################

# Flexible functions for creating congruences
DeclareGlobalFunction("SemigroupCongruence");
DeclareGlobalFunction("LeftSemigroupCongruence");
DeclareGlobalFunction("RightSemigroupCongruence");

# Properties of congruences
DeclareProperty("IsRightSemigroupCongruence", IsLeftSemigroupCongruence);
# DeclareProperty("IsLeftSemigroupCongruence", IsRightSemigroupCongruence);
DeclareProperty("IsSemigroupCongruence", IsLeftSemigroupCongruence);
# DeclareProperty("IsSemigroupCongruence", IsRightSemigroupCongruence);

# Attributes of congruences
DeclareAttribute("NonTrivialEquivalenceClasses", IsEquivalenceRelation);
DeclareAttribute("EquivalenceRelationLookup", IsEquivalenceRelation);
DeclareAttribute("EquivalenceRelationCanonicalLookup", IsEquivalenceRelation);
DeclareAttribute("NrEquivalenceClasses", IsEquivalenceRelation);
DeclareAttribute("EquivalenceRelationCanonicalPartition",
                 IsEquivalenceRelation);
DeclareAttribute("EquivalenceRelationPartitionWithSingletons",
                 IsEquivalenceRelation);

# No-checks version of the "\in" operation
DeclareOperation("CongruenceTestMembershipNC", [IsEquivalenceRelation,
                                                IsMultiplicativeElement,
                                                IsMultiplicativeElement]);

# Algebraic operators
DeclareOperation("JoinLeftSemigroupCongruences",
                 [IsLeftSemigroupCongruence, IsLeftSemigroupCongruence]);
DeclareOperation("JoinRightSemigroupCongruences",
                 [IsRightSemigroupCongruence, IsRightSemigroupCongruence]);

# Comparison operators
DeclareOperation("IsSubrelation",
                 [IsEquivalenceRelation, IsEquivalenceRelation]);
DeclareOperation("IsSuperrelation",
                 [IsEquivalenceRelation, IsEquivalenceRelation]);

########################################################################
# Congruence classes
########################################################################

# Actions
DeclareOperation("OnLeftCongruenceClasses",
                 [IsLeftCongruenceClass, IsMultiplicativeElement]);
DeclareOperation("OnRightCongruenceClasses",
                 [IsRightCongruenceClass, IsMultiplicativeElement]);
