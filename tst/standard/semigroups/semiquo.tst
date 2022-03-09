#############################################################################
##
#W  standard/semigroups/semiquo.tst
#Y  Copyright (C) 2015-2022                              James D. Mitchell 
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
gap> START_TEST("Semigroups package: standard/semigroups/semiquo.tst");
gap> LoadPackage("semigroups", false);;

#
gap> SEMIGROUPS.StartTest();

# quotients, OneImmutable
gap> S := PartitionMonoid(4);
<regular bipartition *-monoid of size 4140, degree 4 with 4 generators>
gap> cong := SemigroupCongruence(S, [S.3, S.4]);
<2-sided semigroup congruence over <regular bipartition *-monoid 
 of size 4140, degree 4 with 4 generators> with 1 generating pairs>
gap> T := S / cong;;
gap> Size(T);
25
gap> One(T);
<2-sided congruence class of <block bijection: [ 1, -1 ], [ 2, -2 ], 
 [ 3, -3 ], [ 4, -4 ]>>

# quotients, GeneratorsOfSemigroup
gap> S := JonesMonoid(5);
<regular bipartition *-monoid of degree 5 with 4 generators>
gap> I := SemigroupIdeal(S, S.4);
<regular bipartition *-semigroup ideal of degree 5 with 1 generator>
gap> J := SemigroupIdeal(I, Bipartition([[1, -3], [2, -4], [3, 4], [5, -5],
> [-1, -2]]));
<regular bipartition *-semigroup ideal of degree 5 with 1 generator>
gap> T := I / J;;
gap> HasGeneratorsOfMagma(T);
false
gap> GeneratorsOfSemigroup(T);
[ <2-sided congruence class of <bipartition: [ 1, -3 ], [ 2, -4 ], [ 3, 4 ], 
     [ 5, -5 ], [ -1, -2 ]>> ]

# quotients, Rees quotient
gap> S := PartitionMonoid(4);
<regular bipartition *-monoid of size 4140, degree 4 with 4 generators>
gap> I := SemigroupIdeal(S, S.4);
<regular bipartition *-semigroup ideal of degree 4 with 1 generator>
gap> T := S / I;;
gap> Size(T);
25

# quotients, PROD_SCL_LIST_DEFAULT, PROD_LIST_SCL_DEFAULT
gap> S := Semigroup([Matrix(IsTropicalMaxPlusMatrix, [[0, 0], [1, 1]], 2),
>  Matrix(IsTropicalMaxPlusMatrix, [[1, 2], [0, -infinity]], 2),
>  Matrix(IsTropicalMaxPlusMatrix, [[2, 2], [1, 0]], 2)]);
<semigroup of 2x2 tropical max-plus matrices with 3 generators>
gap> cong := SemigroupCongruence(S, [S.3, S.1]);
<2-sided semigroup congruence over <non-regular semigroup 
 of size 9, 2x2 tropical max-plus matrices with 3 generators> with 
1 generating pairs>
gap> T := S / cong;;
gap> AsList(T) * T.1;
[ <2-sided congruence class of Matrix(IsTropicalMaxPlusMatrix, 
     [[1, 1], [2, 2]], 2)>, 
  <2-sided congruence class of Matrix(IsTropicalMaxPlusMatrix, 
     [[2, 2], [0, 0]], 2)>, 
  <2-sided congruence class of Matrix(IsTropicalMaxPlusMatrix, 
     [[2, 2], [2, 2]], 2)> ]
gap> T.1 * AsList(T);
[ <2-sided congruence class of Matrix(IsTropicalMaxPlusMatrix, 
     [[1, 1], [2, 2]], 2)>, 
  <2-sided congruence class of Matrix(IsTropicalMaxPlusMatrix, 
     [[1, 2], [2, 2]], 2)>, 
  <2-sided congruence class of Matrix(IsTropicalMaxPlusMatrix, 
     [[2, 2], [2, 2]], 2)> ]
gap> GreensRClasses(S) * T.1;
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `*' on 2 arguments
gap> T.1 * GreensRClasses(S);
Error, no method found! For debugging hints type ?Recovery from NoMethodFound
Error, no 3rd choice method found for `*' on 2 arguments

# quotients, ViewObj
gap> S := Semigroup([Transformation([2, 3, 2]), Transformation([3, 1, 3])]);;
gap> pair := [Transformation([3, 2, 3]), Transformation([1, 1, 1])];;
gap> cong := SemigroupCongruence(S, [pair]);;
gap> Q := S / cong;
<quotient of <2-sided semigroup congruence over <transformation semigroup of 
 degree 3 with 2 generators> with 1 generating pairs>>
gap> Size(Q);
1
gap> I := MinimalIdeal(S);
<simple transformation semigroup ideal of degree 3 with 1 generator>
gap> R := S / I;;
gap> Size(R);
5

# SEMIGROUPS_UnbindVariables
gap> Unbind(I);
gap> Unbind(J);
gap> Unbind(Q);
gap> Unbind(R);
gap> Unbind(S);
gap> Unbind(T);
gap> Unbind(cong);
gap> Unbind(pair);

#
gap> SEMIGROUPS.StopTest();
gap> STOP_TEST("Semigroups package: standard/semigroups/semiquo.tst");
