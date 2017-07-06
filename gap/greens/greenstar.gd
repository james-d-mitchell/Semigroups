#############################################################################
##
#W  greenstar.gd
#Y  Copyright (C) 2017                  James D. Mitchell & Simon Tollman
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

## This file contains the declaration for Green's star relations of
## semigroups.

DeclareCategory("IsGreensStarRelation", IsEquivalenceRelation);
DeclareCategory("IsGreensRStarRelation", IsGreensStarRelation);
DeclareCategory("IsGreensLStarRelation", IsGreensStarRelation);
DeclareCategory("IsGreensJStarRelation", IsGreensStarRelation);
DeclareCategory("IsGreensHStarRelation", IsGreensStarRelation);
DeclareCategory("IsGreensDStarRelation", IsGreensStarRelation);

DeclareAttribute("GreensRStarRelation", IsSemigroup);
DeclareAttribute("GreensLStarRelation", IsSemigroup);
DeclareAttribute("GreensJStarRelation", IsSemigroup);
DeclareAttribute("GreensDStarRelation", IsSemigroup);
DeclareAttribute("GreensHStarRelation", IsSemigroup);

DeclareCategory("IsGreensStarClass", IsEquivalenceClass);
DeclareCategory("IsGreensRStarClass", IsGreensStarClass);
DeclareCategory("IsGreensLStarClass", IsGreensStarClass);
DeclareCategory("IsGreensJStarClass", IsGreensStarClass);
DeclareCategory("IsGreensHStarClass", IsGreensStarClass);
DeclareCategory("IsGreensDStarClass", IsGreensStarClass);

DeclareAttribute("GreensRStarClasses", IsSemigroup);
DeclareAttribute("GreensLStarClasses", IsSemigroup);
DeclareAttribute("GreensJStarClasses", IsSemigroup);
DeclareAttribute("GreensDStarClasses", IsSemigroup);
DeclareAttribute("GreensHStarClasses", IsSemigroup);

DeclareOperation("GreensHStarClass", [IsSemigroup, IsObject]);
DeclareOperation("GreensRStarClass", [IsSemigroup, IsObject]);
DeclareOperation("GreensLStarClass", [IsSemigroup, IsObject]);
DeclareOperation("GreensDStarClass", [IsSemigroup, IsObject]);
DeclareOperation("GreensJStarClass", [IsSemigroup, IsObject]);

DeclareRepresentation("IsGreensStarClassByGreensClassesRep", 
                      IsGreensStarClass and IsAttributeStoringRep, []);

DeclareAttribute("GreensRStarClassType", IsSemigroup);

#DeclareAttribute("GreensHStarClasses", IsGreensStarClass);
#DeclareAttribute("GreensRStarClasses", IsGreensDStarClass);
#DeclareAttribute("GreensLStarClasses", IsGreensDStarClass);

#DeclareAttribute("RStarClass", IsStarClass);
#DeclareAttribute("LStarClass", IsStarClass);
#DeclareAttribute("DStarClass", IsStarClass);
#DeclareAttribute("JStarClass", IsStarClass);

