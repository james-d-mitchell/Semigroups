############################################################################
##
##  congruences/congpairs.gd
##  Copyright (C) 2015-2022                               Michael C. Young
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
## This file contains functions for any semigroup congruence with generating
## pairs.

DeclareAttribute("GeneratingPairsOfAnyCongruence", IsAnyCongruenceCategory);

DeclareSynonym("GeneratingPairsOfLeftSemigroupCongruence",
               GeneratingPairsOfLeftMagmaCongruence);
DeclareSynonym("GeneratingPairsOfRightSemigroupCongruence",
               GeneratingPairsOfRightMagmaCongruence);

DeclareOperation("AsSemigroupCongruenceByGeneratingPairs",
                 [IsSemigroupCongruence]);
DeclareOperation("AsRightSemigroupCongruenceByGeneratingPairs",
                 [IsRightSemigroupCongruence]);
DeclareOperation("AsLeftSemigroupCongruenceByGeneratingPairs",
                 [IsLeftSemigroupCongruence]);

DeclareOperation("AnyCongruenceByGeneratingPairs",
                 [IsSemigroup, IsHomogeneousList, IsFunction]);

# TODO(now) move to cong.gd
DeclareOperation("JoinAnyCongruences",
                 [IsAnyCongruenceCategory, IsAnyCongruenceCategory]);
