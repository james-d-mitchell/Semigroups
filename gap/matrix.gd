############################################################################
##
#W  matrix.gd
#Y  Copyright (C) 2015                                   James D. Mitchell
##                                                         Markus Pfeiffer
##
##  Licensing information can be found in the README file of this package.
##
############################################################################
##

############################################################################
#
# In the best spirit of GAP development we implement our own matrix
# methods.
#
# We declare our own representation so we do not interfere with the GAP
# library or other libraries and dispatch to things we know to work.
#
# This code is based on the IsPlistMatrixRep code from the GAP library
# There is almost no hope whatsoever that we will ever be able to use
# MatrixObj in general for semigroups
#
############################################################################
#
# Our Matrix objects
#
DeclareCategory("IsSMatrix", IsMultiplicativeElementWithInverse and 
                             IsAssociativeElement);
DeclareCategoryCollections("IsSMatrix");
DeclareCategoryCollections("IsSMatrixCollection");

DeclareConstructor("NewSMatrix", [IsSMatrix, IsRing, IsInt, IsList]);
DeclareConstructor("NewSMatrix", [IsSMatrix, IsRing, IsInt, IsPlistMatrixRep]);
DeclareConstructor("NewIdentitySMatrix", [IsSMatrix, IsRing, IsInt]);
DeclareConstructor("NewZeroSMatrix", [IsSMatrix, IsRing, IsInt]);

# These bases are in normal form
DeclareAttribute("RowSpaceBasis", IsSMatrix);
DeclareAttribute("RowSpaceTransformation", IsSMatrix);
DeclareAttribute("RowSpaceTransformationInv", IsSMatrix);
DeclareAttribute("ColSpaceBasis", IsSMatrix);
DeclareAttribute("ColSpaceTransformation", IsSMatrix);
DeclareAttribute("ColSpaceTransformationInv", IsSMatrix);
DeclareAttribute("RightInverse", IsSMatrix);
DeclareAttribute("LeftInverse", IsSMatrix);
DeclareAttribute("DegreeOfSMatrix", IsSMatrix);
DeclareAttribute("RowRank", IsSMatrix);
DeclareAttribute("ColRank", IsSMatrix);
DeclareAttribute("BaseDomain", IsSMatrix);
DeclareAttribute("TransposedMatImmutable", IsSMatrix);
DeclareOperation("AsMatrix", [IsSMatrix]);
DeclareOperation("AsMatrix", [IsMatrixObj]);
DeclareOperation("AsSMatrix", [IsSMatrix, IsMatrix]);
DeclareOperation("AsSMatrix", [IsMatrix]);
DeclareOperation("ConstructingFilter", [IsSMatrix]);

# We might want to store transforming matrices for ColSpaceBasis/RowSpaceBasis?
# We also need operations for acting on Row/Column spaces.

# For the time being we are "happy" with the PlistMatrixRep representation
# as showcased in the library code. Of course we implement our own variant
# of it just to be sure that we duplicate enough code
#
#T Do the rows of our SPlistMatrixRep need to be SPlistRowVectorRep? Or is
#T it good enough to allow IsPlistRowVectorRep?
#
# What about AttributeStoringRep? Is it desirable to just store RowSpaceBasis
# ColumnSpaceBasis as Attributes?
DeclareRepresentation("IsPlistSMatrixRep",
  IsSMatrix and IsComponentObjectRep and IsAttributeStoringRep, []);
BindGlobal("PlistSMatrixFamily", NewFamily("PlistSMatrixFamily",
  IsSMatrix, CanEasilyCompareElements));
BindGlobal("PlistSMatrixType", NewType(PlistSMatrixFamily,
  IsSMatrix and IsPlistSMatrixRep ));

DeclareRepresentation("IsCVECSMatrixRep",
  IsSMatrix and IsComponentObjectRep and IsAttributeStoringRep, []);
BindGlobal("CVECSMatrixFamily", NewFamily("CVECSMatrixFamily",
  IsSMatrix, CanEasilyCompareElements));
BindGlobal("CVECSMatrixType", NewType(CVECSMatrixFamily,
  IsSMatrix and IsCVECSMatrixRep));

DeclareGlobalFunction( "RandomSMatrix" );

DeclareProperty("IsZero", IsSMatrix);
DeclareOperation("OneMutable", [IsSMatrix]);

DeclareOperation("IdentitySMatrix", [IsField and IsFinite, IsInt and IsZero]);
DeclareOperation("IdentitySMatrix", [IsField and IsFinite, IsPosInt]);
DeclareOperation("IdentitySMatrix", [IsSMatrix, IsPosInt]);
DeclareOperation("IdentitySMatrix", [IsField and IsFinite, IsZeroCyc]);
DeclareOperation("TransposedSMat", [IsSMatrix]);
DeclareAttribute("DegreeOfSMatrixCollection", IsSMatrixCollection);
DeclareAttribute("BaseDomain", IsSMatrixCollection);


##
DeclareGlobalFunction("ComputeRowSpaceAndTransformation");
DeclareGlobalFunction("RandomListOfMatricesWithRanks");
DeclareGlobalFunction("RandomSquareSMatrixWithRanks");

## We need a mutable copy of matrices sometimes to do calculations
DeclareGlobalFunction("SEMIGROUPS_MutableCopyMat");
## IsZero is an attribute that is stored, and hence we have 
## this function for debugging purposes that checks whether a 
## matrix is actually zero by inspecting all entries
DeclareGlobalFunction("SEMIGROUPS_CheckReallyZero");
;
