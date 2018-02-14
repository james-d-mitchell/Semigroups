#############################################################################
##
#W  semieunit.gd
#Y  Copyright (C) 2016                                    Christopher Russell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

DeclareCategory("IsMcAlisterTripleSemigroupElement",
                IsAssociativeElement and IsMultiplicativeElementWithInverse);

# This is a representation for McAlister triple semigroup elements, which are
# created via the function McAlisterTripleSemigroupElement.
#
# If x belongs to the representation IsMcAlisterTripleElementRep, then the
# components are:
#
#   x![1]:   The McAlister triple semigroup which this element belongs to
#
#   x![2]:   A vertex of the McAlisterTripleSemigroupSemilattice of x![1]
#
#   x![3]:   An element of the McAlisterTripleSemigroupGroup of x![1]

DeclareRepresentation("IsMcAlisterTripleSemigroupElementRep",
                      IsMcAlisterTripleSemigroupElement
                      and IsPositionalObjectRep, 3);

DeclareCategoryCollections("IsMcAlisterTripleSemigroupElement");
DeclareSynonym("IsMTSE", IsMcAlisterTripleSemigroupElement);
DeclareSynonymAttr("IsMcAlisterTripleSemigroup",
                   IsInverseSemigroup and IsGeneratorsOfInverseSemigroup
                   and IsMcAlisterTripleSemigroupElementCollection
                   and IsWholeFamily and IsActingSemigroup);

DeclareSynonym("IsMcAlisterTripleSubsemigroup",
IsMcAlisterTripleSemigroupElementCollection and IsSemigroup);

# This is a representation for McAlister triple semigroup, which are
# created via the function McAlisterTripleSemigroup.
#
# The attributes stored upon creation are:
#
#   McAlisterTripleSemigroupGroup
#   McAlisterTripleSemigroupPartialOrder
#   McAlisterTripleSemigroupSemilattice
#   McAlisterTripleSemigroupAction
#
# their purpose is described in the section of the user manual on McAlister
# triple semigroups.

DeclareRepresentation("IsMcAlisterTripleSemigroupDefaultRep",
                      IsMcAlisterTripleSemigroup and IsAttributeStoringRep,
                      []);

InstallTrueMethod(IsGeneratorsOfInverseSemigroup,
                  IsMcAlisterTripleSemigroupElementCollection);

# Operations for creating McAlister triple semigroups
DeclareOperation("McAlisterTripleSemigroup",
                 [IsGroup, IsDigraph, IsDigraph, IsFunction]);
DeclareOperation("McAlisterTripleSemigroup",
                 [IsGroup, IsDigraph, IsHomogeneousList, IsFunction]);
DeclareOperation("McAlisterTripleSemigroup",
                 [IsPermGroup, IsDigraph, IsDigraph]);
DeclareOperation("McAlisterTripleSemigroup",
                 [IsPermGroup, IsDigraph, IsHomogeneousList]);

# Attributes for McAlister triple semigroups
DeclareAttribute("McAlisterTripleSemigroupGroup",
                 IsMcAlisterTripleSemigroup and IsWholeFamily);
DeclareAttribute("McAlisterTripleSemigroupAction",
                 IsMcAlisterTripleSemigroup and IsWholeFamily);
DeclareAttribute("McAlisterTripleSemigroupPartialOrder",
                 IsMcAlisterTripleSemigroup and IsWholeFamily);
DeclareAttribute("McAlisterTripleSemigroupSemilattice",
                 IsMcAlisterTripleSemigroup and IsWholeFamily);
# TODO remove this
DeclareAttribute("McAlisterTripleSemigroupElmList",
                 IsMcAlisterTripleSemigroup and IsWholeFamily);
DeclareAttribute("OneImmutable",
                 IsMcAlisterTripleSemigroup and IsWholeFamily and IsMonoid);

DeclareAttribute("McAlisterTripleSemigroupComponents",
                 IsMcAlisterTripleSemigroup and IsWholeFamily);
DeclareAttribute("McAlisterTripleSemigroupQuotientDigraph",
                 IsMcAlisterTripleSemigroup and IsWholeFamily);

# Operations for relating to McAlister triple semigroups
DeclareAttribute("IsomorphismMcAlisterTripleSemigroup",
                IsSemigroup);

# Operations for creating McAlister triple semigroup elements
DeclareOperation("McAlisterTripleSemigroupElement",
                 [IsMcAlisterTripleSemigroup,
                 IsPosInt, IsMultiplicativeElementWithInverse]);
DeclareSynonym("MTSE", McAlisterTripleSemigroupElement);

# Operations for McAlister triple semigroup elements
DeclareAttribute("McAlisterTripleSemigroupElementParent",
                 IsMcAlisterTripleSemigroupElementRep);
DeclareSynonym("MTSEParent", McAlisterTripleSemigroupElementParent);
DeclareOperation("ELM_LIST", [IsMcAlisterTripleSemigroupElementRep, IsPosInt]);

# Inverse semigroup methods
DeclareAttribute("EUnitaryInverseCover", IsSemigroup);
DeclareProperty("IsFInverseSemigroup", IsSemigroup);
DeclareProperty("IsFInverseMonoid", IsSemigroup);
