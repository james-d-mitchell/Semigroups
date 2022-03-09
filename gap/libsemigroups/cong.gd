############################################################################
##
##  libsemigroups/cong.gd
##  Copyright (C) 2022                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
############################################################################

# A congruence satisfies CanUseLibsemigroupsCongruence if it should use a
# libsemigroups Congruence objects to compute things about itself.
DeclareProperty("CanUseLibsemigroupsCongruence",
                IsLeftRightOrTwoSidedCongruence);

# The next operation is the only one supplied by libsemigroups/cong.gd/i that
# is exported.

DeclareOperation("CongruenceLessNC",
                 [CanUseLibsemigroupsCongruence,
                  IsMultiplicativeElement,
                  IsMultiplicativeElement]);
