#############################################################################
##
#W  display.gd
#Y  Copyright (C) 2013-15                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

DeclareOperation("TikzString", [IsObject]);
DeclareOperation("TikzString", [IsObject, IsRecord]);
DeclareOperation("DotString", [IsObject]);
DeclareOperation("DotString", [IsObject, IsRecord]);
DeclareOperation("TexString", [IsObject]);
DeclareOperation("TexString", [IsObject, IsObject]);

DeclareOperation("TikzCayleyDigraph", [IsCayleyDigraph]);
DeclareOperation("TikzLeftCayleyDigraph", [IsSemigroup]);
DeclareOperation("TikzRightCayleyDigraph", [IsSemigroup]);

DeclareOperation("DotCayleyDigraph", [IsCayleyDigraph]);
DeclareOperation("DotLeftCayleyDigraph", [IsSemigroup]);
DeclareOperation("DotRightCayleyDigraph", [IsSemigroup]);

DeclareAttribute("DotSemilatticeOfIdempotents", IsInverseSemigroup);
