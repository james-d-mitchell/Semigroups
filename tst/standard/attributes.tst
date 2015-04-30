#############################################################################
##
#W  attributes.tst
#Y  Copyright (C) 2015                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
gap> START_TEST("Semigroups package: attributes.tst");
gap> LoadPackage("semigroups", false);;

#
gap> SemigroupsStartTest();

#T# AttributesTest1: MultiplicativeZero
# for a transformation semigroup/ideal
gap> t := Transformation([1]);;

# Trivial full transformation monoid T_1
# Previously this crashed: see issue #121 on Bitbucket
gap> s := Semigroup(t); # with displaying the semigroup
<trivial transformation group>
gap> MultiplicativeZero(s) = t;
true
gap> Size(MinimalIdeal(s)) = 1;
true
gap> s := Semigroup(t);; # not displaying the semigroup
gap> MultiplicativeZero(s) = t;
true
gap> Size(MinimalIdeal(s)) = 1;
true
gap> s := FullTransformationMonoid(1);;
gap> MultiplicativeZero(s) = t;
true
gap> Size(MinimalIdeal(s)) = 1;
true

# Trivial transformation monoid with different rep.
gap> t := Transformation([2, 2, 3, 3]);;
gap> s := Semigroup(t); # with displaying the semigroup
<commutative transformation semigroup on 4 pts with 1 generator>
gap> MultiplicativeZero(s) = t;
true
gap> Size(MinimalIdeal(s)) = 1;
true
gap> s := Semigroup(t);; # not displaying the semigroup
gap> MultiplicativeZero(s) = t;
true
gap> Size(MinimalIdeal(s)) = 1;
true

# Issue #121 on Bitbucket (n x 1 rectangular band)
gap> s := Semigroup(Transformation([1, 2, 1]),
>                   Transformation([1, 2, 2]));;
gap> MultiplicativeZero(s);
fail
gap> Size(MinimalIdeal(s)) = 1;
false
gap> ForAny(s, x -> IsMultiplicativeZero(s, x));
false

# Other transformation semigroups
gap> s := Semigroup(FullTransformationMonoid(10), rec(generic := false));
<transformation monoid on 10 pts with 3 generators>
gap> MultiplicativeZero(s);
fail
gap> Size(MinimalIdeal(s)) = 1;
false

# Transformation semigroup ideal
gap> s := Semigroup([
> Transformation([2, 3, 4, 1]),
> Transformation([2, 1, 3, 4]),
> Transformation([3, 1, 1, 3])]);
<transformation semigroup on 4 pts with 3 generators>
gap> t := Transformation([1, 1, 1, 1]);;
gap> I := SemigroupIdeal(s, t);;
gap> HasMultiplicativeZero(s);
false
gap> MultiplicativeZero(I); # does not know whether parent has a zero
fail
gap> Size(MinimalIdeal(I)) = 1;
false
gap> HasMultiplicativeZero(s);
true
gap> MultiplicativeZero(s);
fail
gap> Size(MinimalIdeal(s)) = 1;
false
gap> I := SemigroupIdeal(s, t);;
gap> MultiplicativeZero(I); # does know whether parent has a zero
fail
gap> Size(MinimalIdeal(I)) = 1;
false

#T# AttributesTest2:
# MultiplicativeZero for a partial perm semigroup/ideal
gap> t := PartialPerm([], []);;

# For S = { <empty mapping> }
gap> s := Semigroup(t);;
gap> MultiplicativeZero(s) = t;
true
gap> Size(MinimalIdeal(s)) = 1;
true
gap> s := SymmetricInverseMonoid(1);
<symmetric inverse semigroup on 1 pts>
gap> MultiplicativeZero(s) = t;
true
gap> Size(MinimalIdeal(s)) = 1;
true

# For other trivial partial perm semigroups
gap> t := PartialPerm([2, 4], [2, 4]);;
gap> s := Semigroup(t);;
gap> MultiplicativeZero(s) = t;
true
gap> Size(MinimalIdeal(s)) = 1;
true

# For a non-trivial partial perm semigroup
gap> s := Semigroup([PartialPerm([2], [1])]); # contains <empty pperm>
<commutative partial perm semigroup on 1 pts with 1 generator>
gap> MultiplicativeZero(s);
<empty partial perm>
gap> Size(MinimalIdeal(s)) = 1;
true
gap> s := Semigroup([
> PartialPerm([1, 2, 3], [1, 4, 2]),
> PartialPerm([1, 4], [1, 3])]); # does not contain <empty pperm>
<partial perm semigroup on 4 pts with 2 generators>
gap> MultiplicativeZero(s);
<identity partial perm on [ 1 ]>
gap> Size(MinimalIdeal(s)) = 1;
true
gap> s := InverseSemigroup([
> PartialPerm([1, 2, 3], [3, 4, 1]),
> PartialPerm([1, 2, 3, 4, 5], [3, 5, 1, 2, 4])]);
<inverse partial perm semigroup on 5 pts with 2 generators>
gap> MultiplicativeZero(s);
fail
gap> Size(MinimalIdeal(s)) = 1;
false

# For a partial perm semigroup ideal
gap> s := Semigroup([
> PartialPerm([1, 2, 3, 4], [2, 3, 4, 1]),
> PartialPerm([1, 2, 3, 4], [2, 1, 3, 4]),
> PartialPerm([1, 3], [2, 3])]);
<partial perm semigroup on 4 pts with 3 generators>
gap> t := PartialPerm([], []);;
gap> I := SemigroupIdeal(s, t);;
gap> HasMultiplicativeZero(s);
false
gap> MultiplicativeZero(I) = t; # does not know whether parent has a zero
true
gap> Size(MinimalIdeal(I)) = 1;
true
gap> HasMultiplicativeZero(s);
true
gap> MultiplicativeZero(s) = t;
true
gap> Size(MinimalIdeal(s)) = 1;
true
gap> I := SemigroupIdeal(s, t);;
gap> MultiplicativeZero(I) = t; # does know whether parent has a zero
true
gap> Size(MinimalIdeal(I)) = 1;
true

#T# AttributesTest3:
# MultiplicativeZero for a bipartition semigroup/ideal
gap> s := PartitionMonoid(1);
<commutative bipartition monoid on 1 pts with 1 generator>
gap> MultiplicativeZero(s);
<bipartition: [ 1 ], [ -1 ]>
gap> Size(MinimalIdeal(s)) = 1;
true
gap> s := PartitionMonoid(2);
<regular bipartition monoid on 2 pts with 3 generators>
gap> MultiplicativeZero(s);
fail
gap> Size(MinimalIdeal(s)) = 1;
false
gap> s := PartitionMonoid(3);
<regular bipartition monoid on 3 pts with 4 generators>
gap> MultiplicativeZero(s);
fail
gap> Size(MinimalIdeal(s)) = 1;
false
gap> s := Semigroup([
> Bipartition([[1, 2, 3, 4, 5, -2], [-1], [-3], [-4], [-5]]),
> Bipartition([[1, 3, 5, -1], [2, 4, -2], [-3], [-4], [-5]])]);
<bipartition semigroup on 5 pts with 2 generators>
gap> MultiplicativeZero(s);
<bipartition: [ 1, 2, 3, 4, 5, -2 ], [ -1 ], [ -3 ], [ -4 ], [ -5 ]>
gap> Size(MinimalIdeal(s)) = 1;
true

# Ideals
gap> s := PartitionMonoid(3);;
gap> t := Bipartition([[1, -2], [2], [3, -3], [-1]]);;
gap> I := SemigroupIdeal(s, t);
<regular bipartition semigroup ideal on 3 pts with 1 generator>
gap> HasMultiplicativeZero(s);
false
gap> MultiplicativeZero(I);
fail
gap> Size(MinimalIdeal(I)) = 1;
false
gap> HasMultiplicativeZero(s);
true
gap> MultiplicativeZero(s);
fail
gap> Size(MinimalIdeal(s)) = 1;
false
gap> I := SemigroupIdeal(s, t);;
gap> MultiplicativeZero(I);
fail
gap> Size(MinimalIdeal(I)) = 1;
false
gap> t := Bipartition([[1], [-1]]);;
gap> s := Semigroup([t, Bipartition([[1, -1]])]);;
gap> I := SemigroupIdeal(s, t);;
gap> HasMultiplicativeZero(s);
false
gap> MultiplicativeZero(I);
<bipartition: [ 1 ], [ -1 ]>
gap> Size(MinimalIdeal(I)) = 1;
true
gap> HasMultiplicativeZero(s);
true
gap> MultiplicativeZero(s);
<bipartition: [ 1 ], [ -1 ]>
gap> Size(MinimalIdeal(s)) = 1;
true
gap> I := SemigroupIdeal(s, t);;
gap> MultiplicativeZero(I);
<bipartition: [ 1 ], [ -1 ]>
gap> Size(MinimalIdeal(I)) = 1;
true

#T# AttributesTest4:
# MultiplicativeZero for a block bijection inverse semigroup/ideal
gap> s := AsBlockBijectionSemigroup(SymmetricInverseMonoid(1));
<commutative inverse bipartition monoid on 2 pts with 1 generator>
gap> MultiplicativeZero(s);
<block bijection: [ 1, 2, -1, -2 ]>
gap> Size(MinimalIdeal(s)) = 1;
true
gap> s := AsBlockBijectionSemigroup(SymmetricInverseMonoid(4));
<inverse bipartition monoid on 5 pts with 3 generators>
gap> MultiplicativeZero(s);
<block bijection: [ 1, 2, 3, 4, 5, -1, -2, -3, -4, -5 ]>
gap> Size(MinimalIdeal(s)) = 1;
true
gap> s := InverseSemigroup([
> Bipartition([[1, -3], [2, -4], [3, -1], [4, 5, 6, -2, -5, -6]]),
> Bipartition([[1, -3], [2, -5], [3, -1], [4, -2], [5, -4],
> [6, -6]])]);
<inverse bipartition semigroup on 6 pts with 2 generators>
gap> MultiplicativeZero(s);
fail
gap> Size(MinimalIdeal(s)) = 1;
false

# Ideals
gap> s := InverseSemigroup([
> Bipartition([[1, -1], [2, 6, -4, -6], [3, -5], [4, -2],
>  [5, -3]]),
> Bipartition([[1, -5], [2, -4], [3, -3], [4, -2], [5, -1],
>  [6, -6]])]);
<inverse bipartition semigroup on 6 pts with 2 generators>
gap> t := Bipartition(
> [[1, -1], [2, -2], [3, -3], [4, 6, -4, -6], [5, -5]]);;
gap> I := SemigroupIdeal(s, t);
<inverse bipartition semigroup ideal on 6 pts with 1 generator>
gap> HasMultiplicativeZero(s);
false
gap> MultiplicativeZero(I);
fail
gap> Size(MinimalIdeal(I)) = 1;
false
gap> HasMultiplicativeZero(s);
true
gap> MultiplicativeZero(s);
fail
gap> Size(MinimalIdeal(s)) = 1;
false
gap> I := SemigroupIdeal(s, t);;
gap> MultiplicativeZero(I);
fail
gap> Size(MinimalIdeal(I)) = 1;
false

#T# AttributesTest5:
# MultiplicativeZero where MinimalDClass is known
gap> s := Semigroup(FullTransformationMonoid(10), rec(generic := false));
<transformation monoid on 10 pts with 3 generators>
gap> MinimalDClass(s);;
gap> HasSize(last);
false
gap> MultiplicativeZero(s);
fail
gap> s := Semigroup(s, rec(generic := false));;
gap> HasMinimalDClass(s);
false
gap> Size(MinimalDClass(s));
10
gap> HasMinimalDClass(s) and HasSize(MinimalDClass(s));
true
gap> MultiplicativeZero(s);
fail
gap> gens := [
> Transformation([1, 13, 11, 4, 11, 12, 3, 1, 1, 1, 1, 4, 15, 2, 13]),
> Transformation([3, 11, 14, 4, 11, 13, 13, 5, 3, 11, 14, 14, 10, 15, 12]),
> Transformation([5, 13, 11, 4, 9, 13, 8, 1, 2, 12, 6, 12, 11, 8, 1])];;
gap> s := Semigroup(gens);
<transformation semigroup on 15 pts with 3 generators>
gap> HasMinimalDClass(s);
false
gap> MultiplicativeZero(s);
Transformation( [ 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4 ] )
gap> s := Semigroup(gens, rec(generic := false));;
gap> MinimalDClass(s);
<Green's D-class: Transformation( [ 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
   4 ] )>
gap> HasSize(MinimalDClass(s));
false
gap> MultiplicativeZero(s);
Transformation( [ 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4 ] )
gap> s := Semigroup(gens, rec(generic := false));;
gap> Size(MinimalDClass(s));
1
gap> MultiplicativeZero(s);
Transformation( [ 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4 ] )

#T# attributes: IsomorphismFpMonoid, 
gap> S := Monoid(Transformation([1, 3, 4, 1, 3]),
>                Transformation([2, 4, 1, 5, 5]), 
>                Transformation([2, 5, 3, 5, 3]),
>                Transformation([4, 1, 2, 2, 1]), 
>                Transformation([5, 5, 1, 1, 3]));;
gap> map := IsomorphismFpMonoid(S);
MappingByFunction( <transformation monoid on 5 pts with 5 generators>
 , <fp monoid on the generators [ m1, m2, m3, m4, m5 
 ]>, function( x ) ... end, function( x ) ... end )
gap> inv := InverseGeneralMapping(map);
MappingByFunction( <fp monoid on the generators [ m1, m2, m3, m4, m5 ]>, 
<transformation monoid on 5 pts with 5 generators>
 , function( x ) ... end, function( x ) ... end )
gap> ForAll(S, x -> (x ^ map) ^ inv = x);
true
gap> map := IsomorphismFpSemigroup(S);
MappingByFunction( <transformation monoid on 5 pts with 5 generators>
 , <fp semigroup on the generators [ s1, s2, s3, s4, s5, s6 
 ]>, function( x ) ... end, function( x ) ... end )
gap> inv := InverseGeneralMapping(map);
MappingByFunction( <fp semigroup on the generators [ s1, s2, s3, s4, s5, s6 
 ]>, <transformation monoid on 5 pts with 5 generators>
 , function( x ) ... end, function( x ) ... end )
gap> ForAll(S, x -> (x ^ map) ^ inv = x);
true

#T# attributes: RightCayleyGraphSemigroup
gap> S := Semigroup(PartialPerm([1, 2, 3], [1, 3, 4]),
>                   PartialPerm([1, 2, 3], [2, 5, 3]),
>                   PartialPerm([1, 2, 3], [4, 1, 2]),
>                   PartialPerm([1, 2, 3, 4], [2, 4, 1, 5 ]),
>                   PartialPerm([1, 3, 5], [5, 1, 3]));;
gap> RightCayleyGraphSemigroup(S);;
gap> Length(STRONGLY_CONNECTED_COMPONENTS_DIGRAPH(last)) = NrRClasses(S);
true

#T# attributes: LeftCayleyGraphSemigroup
gap> S := Monoid(BooleanMatNC([[1, 1, 1, 1, 1], [1, 0, 1, 0, 0],
>                              [1, 1, 0, 1, 0], [1, 1, 1, 1, 1],
>                              [1, 1, 0, 0, 0]]),
>                BooleanMatNC([[0, 0, 1, 0, 0], [1, 0, 1, 1, 0],
>                              [1, 0, 1, 1, 1], [0, 1, 1, 1, 0],
>                              [0, 1, 1, 1, 0]]),
>                BooleanMatNC([[0, 0, 0, 1, 1], [0, 0, 1, 1, 0],
>                              [0, 0, 1, 1, 0], [1, 1, 0, 1, 0],
>                              [1, 0, 1, 0, 1]]),
>                BooleanMatNC([[0, 1, 1, 1, 0], [0, 0, 0, 1, 0],
>                              [1, 1, 1, 0, 1], [1, 0, 1, 0, 0],
>                              [1, 0, 1, 1, 0]]),
>                BooleanMatNC([[1, 0, 0, 0, 1], [1, 0, 0, 0, 1],
>                              [0, 0, 0, 0, 1], [0, 1, 1, 0, 1],
>                              [1, 1, 1, 0, 1]]));;
gap> LeftCayleyGraphSemigroup(S);;
gap> Length(STRONGLY_CONNECTED_COMPONENTS_DIGRAPH(last)) = NrLClasses(S);
true

#T# attributes: IsomorphismReesMatrixSemigroup
gap> D := GreensDClassOfElement(Semigroup(
> Bipartition([[1, 2, 3, -3], [4, -4, -5], [5, -1], [-2]]),
> Bipartition([[1, 4, -2, -3], [2, 3, 5, -5], [-1, -4]]),
> Bipartition([[1, 5], [2, 4, -3, -5], [3, -1, -2], [-4]]),
> Bipartition([[1], [2], [3, 5, -1, -2], [4, -3], [-4, -5]]),
> Bipartition([[1], [2], [3], [4, -1, -4], [5], [-2, -3], [-5]])), 
> Bipartition([[1], [2], [3], [4, -1, -4], [5], [-2, -3], [-5]]));;
gap> IsomorphismReesMatrixSemigroup(D);
MappingByFunction( <Green's D-class: <bipartition: [ 1 ], [ 2 ], [ 3 ], 
  [ 4, -1, -4 ], [ 5 ], [ -2, -3 ], [ -5 ]>>, 
<Rees 0-matrix semigroup 12x15 over Group(())>
 , function( x ) ... end, function( x ) ... end )

#T# attributes: IrredundantGeneratingSubset, for a collection of elements
gap> G := CyclicGroup(3);;
gap> R := GF(2);;
gap> GR := GroupRing(R, G);;
gap> iso := IsomorphismTransformationSemigroup(GR);;
gap> S := Range(iso);;
gap> S := Semigroup(IrredundantGeneratingSubset(SmallGeneratingSet(S)));;

#T# attributes: IrredundantGeneratingSubset: for a semigroup
gap> S := RandomBooleanMatMonoid(10, 3);;
gap> T := Semigroup(IrredundantGeneratingSubset(S));;
gap> S = T;
true

#T# attributes: IrredundantGeneratingSubset: for a set with one element
gap> IrredundantGeneratingSubset([RandomTransformation(10)]);;

#T# attributes: IrredundantGeneratingSubset: for a set with one element
gap> S := Monoid( [ Transformation( [ 1, 1 ] ), Transformation( [ 2, 1 ] ),
>  Transformation( [ 2, 2 ] ) ], rec(generic := false) );
<transformation monoid on 2 pts with 3 generators>
gap> SetInfoLevel(InfoSemigroups, 3);
gap> IrredundantGeneratingSubset(S);;
at 	1 of 	4 with 	0 redundant, 	0 non-redundant
at 	2 of 	4 with 	0 redundant, 	1 non-redundant
at 	3 of 	4 with 	1 redundant, 	1 non-redundant
at 	4 of 	4 with 	2 redundant, 	1 non-redundant

gap> SetInfoLevel(InfoSemigroups, 0);

#T# attributes: IsomorphismReesMatrixSemigroup: for a simple semigroup
gap> S := SemigroupIdeal( Semigroup(
>     [ Bipartition( [ [ 1, 2, 3, 6, 7, 8, -2, -4, -5, -6 ], [ 4, 5, -1, -8 ], [ -3 ],
>         [ -7 ] ] ),
>        Bipartition( [ [ 1, 5, 8 ], [ 2, 7, -3, -6 ], [ 3, 4, -4, -7 ], [ 6, -1, -5 ],
>         [ -2, -8 ] ] ) ]
>        ), [ Bipartition( [ [ 1, 2, 3, 4, 5, 6, 7, 8, -1, -2, -4, -5, -6, -8 ],
>       [ -3 ], [ -7 ] ] ) ] );;
gap> IsomorphismReesMatrixSemigroup(S);;

#T# attributes: IsomorphismReesMatrixSemigroup: for a 0-simple semigroup 1/2
gap> S := Semigroup( [ Transformation( [ 1, 1, 5, 1, 3, 1, 9, 1, 7, 5 ] ),
>   Transformation( [ 1, 1, 2, 1, 4, 1, 6, 1, 8, 2 ] ),
>   Transformation( [ 1, 5, 1, 3, 1, 9, 1, 7, 1, 7 ] ) ] );;
gap> IsomorphismReesMatrixSemigroup(S);;

#T# attributes: IsomorphismReesMatrixSemigroup: for a 0-simple semigroup 2/2
gap> S := Semigroup( [ Transformation( [ 1, 1, 5, 1, 3, 1, 9, 1, 7, 5 ] ),
>   Transformation( [ 1, 1, 2, 1, 4, 1, 6, 1, 8, 2 ] ),
>   Transformation( [ 1, 5, 1, 3, 1, 9, 1, 7, 1, 7 ] ) ] );;
gap> S := Semigroup(MultiplicativeZero(S), S);;
gap> IsomorphismReesMatrixSemigroup(S);;

#T# attributes: IsomorphismReesMatrixSemigroup: for a non-simple or non-0-simple
gap> S := Semigroup(Transformation( [ 2, 1 ] ), Transformation( [ 2, 2 ] ));;
gap> IsomorphismReesMatrixSemigroup(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 4th choice method found for `IsomorphismReesMatrixSemigroup' on 1 ar\
guments

#T# attributes: PrincipalFactor: for a D-class
gap> D := GreensDClassOfElement(
>       Semigroup(
>          BooleanMatNC([[0, 1, 1, 0, 1, 0], [0, 1, 0, 1, 0, 0], [1, 1, 1, 0, 0, 0],
>             [0, 1, 1, 1, 1, 1], [1, 0, 1, 0, 0, 1], [1, 0, 1, 0, 1, 1]]),
>          BooleanMatNC([[1, 1, 1, 1, 1, 0], [0, 0, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0],
>             [1, 0, 1, 1, 1, 0], [1, 1, 1, 0, 0, 1], [1, 1, 0, 0, 0, 0]]) ),
>      BooleanMatNC([[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1],
>         [1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1]]));;
gap> PrincipalFactor(D);
<Rees matrix semigroup 1x1 over Group(())>

#T# attributes: SmallSemigroupGeneratingSet: for a collection with > 1 elements
gap> SmallSemigroupGeneratingSet([
> Transformation( [ 1, 1, 1, 1, 4 ] ), Transformation( [ 1, 2, 2, 1, 1 ] ),
> Transformation( [ 1, 2, 5, 4, 4 ] ), Transformation( [ 1, 3, 3, 5, 1 ] ),
> Transformation( [ 2, 2, 1, 2, 4 ] ), Transformation( [ 3, 2, 3, 3, 2 ] ),
> Transformation( [ 3, 5, 2, 4, 4 ] ), Transformation( [ 3, 5, 4, 5, 4 ] ),
> Transformation( [ 4, 4, 2, 5, 5 ] ), Transformation( [ 5, 2, 3, 5, 2 ] ) ]);;

#T# attributes: SmallSemigroupGeneratingSet: for a collection with 1 elements
gap> SmallSemigroupGeneratingSet([BooleanMatNC([[0, 1, 0, 0], [0, 1, 1, 0], [0,
> 1, 0, 0], [1, 0, 1, 1]])]);
[ <4x4 boolean matrix> ]

#T# attributes: SmallSemigroupGeneratingSet: for a semigroup
gap> S := Semigroup( [ PartialPerm( [ 1, 2 ], [ 3, 2 ] ),
> PartialPerm( [ 1, 2, 3 ], [ 2, 3, 4 ] ), 
> PartialPerm( [ 1, 2, 3 ], [ 2, 5, 3 ] ),
> PartialPerm( [ 1, 4 ], [ 1, 3 ] ), 
> PartialPerm( [ 1, 2, 3, 4 ], [ 3, 5, 1, 2 ] ),
> PartialPerm( [ 1, 2, 3, 4 ], [ 5, 4, 2, 1 ] ),
> PartialPerm( [ 1, 3, 5 ], [ 1, 4, 2 ] ),
> PartialPerm( [ 1, 2, 4, 5 ], [ 3, 2, 5, 1 ] ),
> PartialPerm( [ 1, 2, 4, 5 ], [ 3, 5, 1, 2 ] ),
> PartialPerm( [ 1, 3, 5 ], [ 4, 3, 1 ] ) ] );;
gap> SmallSemigroupGeneratingSet(S);;

#T# attributes: SmallMonoidGeneratingSet: for a singleton set 1/2
gap> SmallMonoidGeneratingSet([IdentityTransformation]);
[  ]

#T# attributes: SmallMonoidGeneratingSet: for a singleton set 2/2
gap> SmallMonoidGeneratingSet([Transformation([2,1,2])]);
[ Transformation( [ 2, 1, 2 ] ) ]

#T# attributes: SmallMonoidGeneratingSet: for a 0 generator monoid
gap> S := Monoid( Bipartition( [ [ 1, -1 ] ] ) );;
gap> SmallMonoidGeneratingSet(S);
[  ]

#T# attributes: SmallInverseSemigroupGeneratingSet: for collection > 1 element 
gap> SmallInverseSemigroupGeneratingSet(
> [ PartialPerm( [ 1, 2 ], [ 4, 1 ] ),
>   PartialPerm( [ 1, 2 ], [ 5, 2 ] ), PartialPerm( [ 1, 2, 3 ], [ 3, 2, 1 ] ),
>   PartialPerm( [ 1, 2, 3 ], [ 3, 2, 4 ] ),
>   PartialPerm( [ 1, 2, 3, 4 ], [ 1, 2, 3, 5 ] ),
>   PartialPerm( [ 1, 3, 4 ], [ 3, 2, 1 ] ), PartialPerm( [ 1, 2, 4 ], [ 3, 1, 2 ] ),
>   PartialPerm( [ 1, 2, 3, 4, 5 ], [ 3, 1, 5, 4, 2 ] ),
>   PartialPerm( [ 1, 2, 3, 5 ], [ 5, 4, 2, 3 ] ) ] );;

#T# attributes: SmallInverseSemigroupGeneratingSet: for collection 1 element 
gap> SmallInverseSemigroupGeneratingSet( [ PartialPerm( [ 1, 2, 3, 7, 9, 10,
> 11, 12 ], [ 4, 6, 8, 12, 5, 9, 1, 3 ] ) ] );
[ [2,6][7,12,3,8][10,9,5][11,1,4] ]

#T# attributes: SmallInverseSemigroupGeneratingSet: for an inverse semigroup
gap> S := 
> InverseSemigroup( [ PartialPerm( [ 1, 2 ], [ 1, 2 ] ),
>   PartialPerm( [ 1, 2, 4 ], [ 2, 3, 1 ] ), PartialPerm( [ 1, 3, 4 ], [ 3, 2, 4 ] ),
>   PartialPerm( [ 1, 2, 4, 5 ], [ 1, 3, 5, 4 ] ),
>   PartialPerm( [ 1, 2, 4, 5 ], [ 2, 1, 3, 5 ] ),
>   PartialPerm( [ 1, 3, 5 ], [ 3, 1, 2 ] ),
>   PartialPerm( [ 1, 2, 3, 5 ], [ 3, 1, 2, 5 ] ),
>   PartialPerm( [ 1, 2, 3, 4, 5 ], [ 3, 5, 1, 2, 4 ] ),
>   PartialPerm( [ 1, 3, 5 ], [ 4, 3, 2 ] ),
>   PartialPerm( [ 1, 2, 3, 5 ], [ 4, 1, 2, 3 ] ) ] );;
gap> SmallInverseSemigroupGeneratingSet(S);;

#T# attributes: SmallInverseMonoidGeneratingSet: for 0 generators
gap> S := InverseMonoid(PartialPerm([1, 2, 3]));
<trivial partial perm group on 3 pts with 0 generators>
gap> SmallInverseMonoidGeneratingSet(S);
[  ]

#T# attributes: SmallInverseMonoidGeneratingSet: for > 0 generators 1/2
gap> S := InverseMonoid( [ PartialPerm( [ 1, 3 ], [ 2, 3 ] ),
>  PartialPerm( [ 1, 3 ], [ 3, 1 ] ), 
>  PartialPerm( [ 1, 2, 3 ], [ 3, 2, 4 ] ),
>  PartialPerm( [ 1, 4 ], [ 1, 3 ] ) ] );;
gap> SmallInverseMonoidGeneratingSet(S);;

#T# attributes: SmallInverseMonoidGeneratingSet: for > 0 generators 2/2
gap> SmallInverseMonoidGeneratingSet(DualSymmetricInverseMonoid(3));
[ <block bijection: [ 1, -2 ], [ 2, -1 ], [ 3, -3 ]>, 
  <block bijection: [ 1, -2 ], [ 2, -3 ], [ 3, -1 ]>, 
  <block bijection: [ 1, 2, -3 ], [ 3, -1, -2 ]> ]

#T# attributes: SmallInverseSemigroupGeneratingSet: for a collection
gap> coll := [ Bipartition( [ [ 1, -1 ], [ 2, -2 ], [ 3, -3 ], [ 4, -4 ], [ 5, -5 ] ] ),
>  Bipartition( [ [ 1, -1 ], [ 2, -4 ], [ 3, -3 ], [ 4 ], [ 5 ], [ -2 ], [ -5 ] ] ),
>  Bipartition( [ [ 1, -2 ], [ 2, -4 ], [ 3, -3 ], [ 4 ], [ 5 ], [ -1 ], [ -5 ] ] ),
>  Bipartition( [ [ 1, -3 ], [ 2, -4 ], [ 3 ], [ 4, -1 ], [ 5 ], [ -2 ], [ -5 ] ] ),
>  Bipartition( [ [ 1, -1 ], [ 2, -2 ], [ 3 ], [ 4, -4 ], [ 5, -3 ], [ -5 ] ] ),
>  Bipartition( [ [ 1, -1 ], [ 2, -5 ], [ 3, -4 ], [ 4 ], [ 5, -2 ], [ -3 ] ] ),
>  Bipartition( [ [ 1, -3 ], [ 2 ], [ 3, -5 ], [ 4, -2 ], [ 5, -4 ], [ -1 ] ] ),
>  Bipartition( [ [ 1, -3 ], [ 2, -1 ], [ 3, -5 ], [ 4 ], [ 5, -2 ], [ -4 ] ] ),
>  Bipartition( [ [ 1, -4 ], [ 2 ], [ 3 ], [ 4, -1 ], [ 5, -5 ], [ -2 ], [ -3 ] ] ),
>  Bipartition( [ [ 1, -5 ], [ 2 ], [ 3, -1 ], [ 4, -2 ], [ 5, -3 ], [ -4 ] ] ),
>  Bipartition( [ [ 1, -5 ], [ 2, -3 ], [ 3 ], [ 4, -4 ], [ 5, -1 ], [ -2 ] ] ),
>  Bipartition( [ [ 1, -1 ], [ 2 ], [ 3, -3 ], [ 4, -2 ], [ 5 ], [ -4 ], [ -5 ] ] ),
>  Bipartition( [ [ 1 ], [ 2, -1 ], [ 3, -3 ], [ 4, -2 ], [ 5 ], [ -4 ], [ -5 ] ] ),
>  Bipartition( [ [ 1, -4 ], [ 2 ], [ 3, -1 ], [ 4, -2 ], [ 5 ], [ -3 ], [ -5 ] ] ),
>  Bipartition( [ [ 1, -1 ], [ 2, -2 ], [ 3, -5 ], [ 4, -4 ], [ 5 ], [ -3 ] ] ),
>  Bipartition( [ [ 1, -1 ], [ 2, -5 ], [ 3 ], [ 4, -3 ], [ 5, -2 ], [ -4 ] ] ),
>  Bipartition( [ [ 1 ], [ 2, -4 ], [ 3, -1 ], [ 4, -5 ], [ 5, -3 ], [ -2 ] ] ),
>  Bipartition( [ [ 1, -3 ], [ 2, -4 ], [ 3, -5 ], [ 4 ], [ 5, -1 ], [ -2 ] ] ),
>  Bipartition( [ [ 1, -5 ], [ 2 ], [ 3, -2 ], [ 4, -4 ], [ 5, -1 ], [ -3 ] ] ) ];;
gap> SmallInverseSemigroupGeneratingSet(coll);;

#T# attributes: SmallInverseMonoidGeneratingSet: for a collection
gap> coll := [ PartialPerm( [ 1, 2, 3, 4, 5 ], [ 1, 2, 3, 4, 5 ] ),
> PartialPerm( [ 1, 2 ], [ 1, 4 ] ), PartialPerm( [ 1, 2, 3 ], [ 1, 4, 2 ] ),
> PartialPerm( [ 1, 2, 3 ], [ 3, 5, 2 ] ),
> PartialPerm( [ 1, 2, 3, 4 ], [ 1, 5, 4, 2 ] ),
> PartialPerm( [ 1, 2, 4 ], [ 2, 3, 1 ] ), PartialPerm( [ 1, 3, 4 ], [ 3, 2, 4 ] ),
> PartialPerm( [ 1, 2, 3, 4 ], [ 5, 2, 3, 4 ] ),
> PartialPerm( [ 1, 2, 4, 5 ], [ 1, 3, 5, 4 ] ),
> PartialPerm( [ 1, 3, 5 ], [ 3, 1, 2 ] ),
> PartialPerm( [ 1, 2, 4, 5 ], [ 5, 3, 2, 1 ] ), PartialPerm( [ 1, 4 ], [ 1, 2 ] ),
> PartialPerm( [ 1, 2, 4 ], [ 1, 3, 2 ] ), PartialPerm( [ 2, 3, 5 ], [ 3, 1, 2 ] ),
> PartialPerm( [ 1, 2, 4, 5 ], [ 1, 4, 3, 2 ] ),
> PartialPerm( [ 1, 2, 3 ], [ 4, 1, 2 ] ), PartialPerm( [ 2, 3, 4 ], [ 3, 1, 4 ] ),
> PartialPerm( [ 2, 3, 4, 5 ], [ 2, 3, 4, 1 ] ),
> PartialPerm( [ 1, 3, 4, 5 ], [ 1, 2, 5, 4 ] ),
> PartialPerm( [ 1, 2, 3 ], [ 3, 5, 1 ] ),
> PartialPerm( [ 1, 2, 3, 5 ], [ 5, 4, 2, 1 ] ) ];;
gap> SmallInverseMonoidGeneratingSet(coll);;

#T# attributes: SmallInverseMonoidGeneratingSet: for a collection of 1 element
gap> SmallInverseMonoidGeneratingSet([PartialPerm([1,2,4])]);
[ [3,4](1)(2) ]

#T# attributes: SmallInverseSemigroupGeneratingSet: for non-inverse-op elements
gap> SmallInverseSemigroupGeneratingSet([RandomTransformation(10)]);
Error, Semigroups: SmallInverseSemigroupGeneratingSet: usage
the argument must satisfy IsGeneratorsOfInverseSemigroup

#T# attributes: SmallInverseMonoidGeneratingSet: for non-inverse-op elements
gap> SmallInverseMonoidGeneratingSet([RandomBooleanMat(10)]);
Error, Semigroups: SmallInverseMonoidGeneratingSet: usage
the argument must satisfy IsGeneratorsOfInverseSemigroup

#T# attributes: SmallInverseMonoidGeneratingSet: for One
gap> SmallInverseMonoidGeneratingSet([PartialPerm([1, 2, 3])]);
[  ]

#T# attributes: SmallGeneratingSet: for an ideal
gap> S := SemigroupIdeal( Semigroup(
>     BooleanMatNC([[0, 1, 0], [1, 0, 0], [0, 0, 1]]),
>     BooleanMatNC([[0, 1, 0], [0, 0, 1], [1, 0, 0]]),
>     BooleanMatNC([[1, 0, 0], [0, 1, 0], [1, 0, 1]]),
>     BooleanMatNC([[1, 0, 0], [0, 1, 0], [0, 0, 0]]) ),
> BooleanMatNC([[1, 0, 0], [0, 0, 0], [1, 1, 0]]) );;
gap> SmallGeneratingSet(S);
[ <3x3 boolean matrix> ]

#T# attributes: SmallGeneratingSet: for a group
gap> S := Group(IdentityTransformation);
<transformation group with 1 generator>
gap> SmallGeneratingSet(S);
[ IdentityTransformation ]

#T# attributes: SmallGeneratingSet: for an inverse monoid
gap> S := InverseMonoid( [ PartialPerm( [ 1, 2 ], [ 3, 2 ] ),
>  PartialPerm( [ 1, 2, 4 ], [ 2, 3, 1 ] ), PartialPerm( [ 1, 2, 4 ], [ 3, 4, 2 ] ),
>  PartialPerm( [ 1, 4 ], [ 4, 2 ] ) ] );;
gap> SmallGeneratingSet(S);;

#T# attributes: SmallGeneratingSet: for an inverse semigroup
gap> S := InverseSemigroup( [ PartialPerm( [ 1, 2 ], [ 2, 3 ] ),
>                             PartialPerm( [ 1, 3 ], [ 3, 1 ] ), 
>                             PartialPerm( [ 1, 2, 3 ], [ 4, 3, 2 ] ) ] );;
gap> SmallGeneratingSet(S);;

#T# attributes: SmallGeneratingSet: for a semigroup 
gap> S := Semigroup( [ Transformation( [ 3, 1, 4, 1, 3 ] ),
>                      Transformation( [ 3, 5, 3, 2, 4 ] ) ] );;
gap> SmallGeneratingSet(S);;

#T# attributes: StructureDescription for a Brandt semigroup
gap> S := SemigroupIdeal( InverseSemigroup(
>  [ PartialPermNC( [ 1, 2, 3, 4 ], [ 4, 1, 2, 6 ] ), 
>    PartialPermNC( [ 1, 2, 4 ], [ 5, 2, 3 ] ), 
>    PartialPermNC( [ 1, 2, 3, 6 ], [ 1, 3, 4, 5 ] ), 
>    PartialPermNC( [ 1, 2, 3, 4, 6 ], [ 2, 4, 6, 1, 5 ] ), 
>    PartialPermNC( [ 1, 2, 3, 6 ], [ 5, 1, 6, 3 ] ) ] ),
>   [ PartialPermNC( [ 2 ], [ 2 ] ) ] );;
gap> IsBrandtSemigroup(S);
true
gap> StructureDescription(S);
"B(1, 6)"

#T# attributes: StructureDescription for a group as semigroup 1/3
gap> S := AsTransformationSemigroup(AlternatingGroup(5));;
gap> IsGroupAsSemigroup(S);
true
gap> StructureDescription(S);
"A5"

#T# attributes: StructureDescription for a group as semigroup 2/3
gap> S := Semigroup(Transformation([2,1,1]));
<commutative transformation semigroup on 3 pts with 1 generator>
gap> IsGroupAsSemigroup(S);
true
gap> StructureDescription(S);
"C2"

#T# attributes: StructureDescription for a group as semigroup 3/3
gap> S := SymmetricGroup(3);;
gap> StructureDescription(S);
"S3"

#T# attributes: IsGreensDLeq
gap> S := RegularBooleanMatSemigroup(3);;
gap> foo := IsGreensDLeq(S);
function( x, y ) ... end
gap> x := BooleanMatNC([[1, 0, 1], [1, 1, 0], [1, 0, 1]]);;
gap> y := BooleanMatNC([[1, 0, 1], [0, 0, 0], [1, 0, 0]]);;
gap> foo(x, y);
true
gap> foo(y, x);
false
gap> z := RepresentativeOfMinimalIdeal(S);
<3x3 boolean matrix>
gap> foo(x, z);
true
gap> foo(z, x);
false
gap> foo(z, y);
false
gap> foo(y, z);
true

#T# attributes: MaximalDClasses
gap> S := RegularBooleanMatSemigroup(3);
<semigroup of 3x3 boolean matrices with 4 generators>
gap> MaximalDClasses(S);
[ <Green's D-class: <3x3 boolean matrix>> ]

#T# attributes: StructureDescriptionMaximalSubgroups
gap> S := RegularBooleanMatSemigroup(3);;
gap> StructureDescriptionMaximalSubgroups(S);
[ "1", "C2", "S3" ]

#T# attributes: IdempotentGeneratedSubsemigroup
gap> S := RegularBooleanMatSemigroup(3);;
gap> IdempotentGeneratedSubsemigroup(S);
<monoid of 3x3 boolean matrices with 122 generators>

#T# attributes: InjectionPrincipalFactor
gap> S := Monoid( [ BooleanMatNC([[1, 0, 1], [0, 1, 0], [0, 0, 1]]),
>   BooleanMatNC([[1, 0, 0], [0, 1, 1], [0, 0, 1]]),
>   BooleanMatNC([[1, 0, 0], [0, 1, 0], [1, 0, 1]]),
>   BooleanMatNC([[1, 0, 0], [0, 1, 0], [0, 1, 1]]),
>   BooleanMatNC([[1, 0, 0], [1, 1, 0], [0, 0, 1]]),
>   BooleanMatNC([[1, 1, 0], [0, 1, 0], [0, 0, 1]]),
>   BooleanMatNC([[1, 1, 0], [0, 0, 0], [0, 1, 1]]),
>   BooleanMatNC([[1, 0, 1], [0, 1, 0], [0, 0, 0]]),
>   BooleanMatNC([[1, 0, 0], [0, 0, 1], [0, 0, 1]]),
>   BooleanMatNC([[0, 0, 0], [0, 1, 0], [0, 0, 1]]),
>   BooleanMatNC([[1, 0, 0], [0, 0, 0], [0, 0, 1]]),
>   BooleanMatNC([[1, 0, 0], [0, 1, 0], [0, 0, 0]]) ] );;
gap> D := DClass(S, BooleanMatNC([[1, 0, 1], [1, 1, 1], [1, 0, 1]]));;
gap> map := InjectionPrincipalFactor(D);
MappingByFunction( <Green's D-class: <3x3 boolean matrix>>, 
<Rees 0-matrix semigroup 12x12 over Group(())>
 , function( x ) ... end, function( x ) ... end )
gap> inv := InverseGeneralMapping(map);;
gap> ForAll(D, x -> (x ^ map) ^ inv = x);
true
gap> MultiplicativeZero(Range(map)) ^ inv;
fail
gap> x := BooleanMatNC([[0, 0, 0], [1, 1, 0], [0, 0, 0]]);;
gap> x ^ map;
fail
gap> D := First(DClasses(S), x-> not IsRegularClass(x));
<Green's D-class: <3x3 boolean matrix>>
gap> InjectionPrincipalFactor(D);
Error, Semigroups: InjectionPrincipalFactor: usage,
the argument <D> must be a regular D-class,

#T# attributes: MultiplicativeNeutralElement
gap> S := Semigroup( [ BooleanMatNC([[0, 0, 1], [0, 0, 1], [0, 1, 1]]),
>  BooleanMatNC([[1, 0, 0], [1, 1, 0], [0, 1, 1]]) ] );;
gap> MultiplicativeNeutralElement(S);
fail
gap> S := Semigroup(AsBooleanMat(Transformation([2,1,2]), 3));;
gap> Display(MultiplicativeNeutralElement(S));
1 0 0
0 1 0
1 0 0
gap> S := RegularBooleanMatSemigroup(2);
<semigroup of 2x2 boolean matrices with 4 generators>
gap> MultiplicativeNeutralElement(S);
<2x2 boolean matrix>

#T# attributes: IsomorphismPermGroup
gap> S := RegularBooleanMatSemigroup(2);
<semigroup of 2x2 boolean matrices with 4 generators>
gap> IsomorphismPermGroup(S);
Error, Semigroups: IsomorphismPermGroup: usage,
the argument must be a semigroup satisfying IsGroupAsSemigroup,
gap> S := Semigroup( [ BooleanMatNC([[0, 1, 0], [1, 0, 0], [0, 0, 1]]),
>  BooleanMatNC([[0, 1, 0], [0, 0, 1], [1, 0, 0]]) ] );;
gap> IsomorphismPermGroup(S);
MappingByFunction( <simple semigroup of 3x3 boolean matrices with 2 generators
>, Group([ (1,2)(3,5)(4,6), (1,5,4)
(2,6,3) ]), function( x ) ... end, function( x ) ... end )

#T# attributes: GroupOfUnits, for a finite semigroup 1/2
gap> S := RegularBooleanMatSemigroup(3);
<semigroup of 3x3 boolean matrices with 4 generators>
gap> GroupOfUnits(S);
<simple monoid of 3x3 boolean matrices with 2 generators>
gap> StructureDescription(last);
"S3"

#T# attributes: GroupOfUnits, fail 2/2
gap> S := Semigroup(
> BooleanMatNC([[1, 1, 0, 1], [0, 1, 1, 0], [1, 1, 0, 1], [1, 1, 0, 1]]),
> BooleanMatNC([[1, 1, 0, 1], [0, 1, 1, 1], [0, 1, 1, 1], [0, 1, 1, 0]]));;
gap> GroupOfUnits(S);
fail

#T# SEMIGROUPS_UnbindVariables
gap> Unbind(s);
gap> Unbind(t);
gap> Unbind(I);
gap> Unbind(gens);

#E#
gap> STOP_TEST("Semigroups package: attributes.tst");