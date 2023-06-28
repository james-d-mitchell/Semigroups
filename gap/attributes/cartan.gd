

#! @Chapter Representation theory

#! Blah blah

DeclareAttribute("MonoidCartanMatrix", IsMonoid);
DeclareAttribute("TransversalIdempotents", IsSemigroup);
DeclareAttribute("SConjugacyClassReps", IsSemigroup);
DeclareAttribute("ConcatenatedLClassBicharacters", IsSemigroup);
DeclareAttribute("ConcatenatedRClassBicharacters", IsSemigroup);

DeclareOperation("DClassBicharacter", 
                 [IsSemigroup, IsMultiplicativeElement, IsList]);
DeclareOperation("LClassBicharacter",
                 [IsSemigroup, IsMultiplicativeElement, IsList]);
DeclareOperation("RClassBicharacter",
                 [IsSemigroup, IsMultiplicativeElement, IsList]);


DeclareOperation("RClassRadical",
                 [IsSemigroup, IsMultiplicativeElement, IsList]);
DeclareOperation("RClassRadicalBicharacter",
                 [IsSemigroup, IsMultiplicativeElement]);
                 
# ConcatenatedRClassRadicalBicharacters 
# DiagonalOfCharacterTables 
# MonoidCharacterTable 

