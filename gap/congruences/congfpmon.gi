############################################################################
##
#W  congruences/congfpmon.gi
#Y  Copyright (C) 2017                                   Michael C. Torpey
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
## This file contains methods for congruences (left, right, or 2-sided) defined
## by generating pairs on finitely presented monoids.  The approach is, on
## creation, to take an isomorphism to an fp semigroup, and then to call the
## standard methods defined in congpairs.gd/gi to answer any questions about the
## congruence.
##

# The argument <cong> is a congruence on an fp monoid, and this function
# returns the class of <cong> corresponding to <semiclass>.

SEMIGROUPS.FpMonClassFromFpSemiClass := function(cong, semiclass)
  local filt, fam, class, map;

  if IsCongruenceClass(semiclass) then
    filt := IsCongruenceClass;
  elif IsLeftCongruenceClass(semiclass) then
    filt := IsLeftCongruenceClass;
  else
    filt := IsRightCongruenceClass;
  fi;

  fam := FamilyObj(Range(cong));
  class := Objectify(NewType(fam, IsFpMonoidCongruenceClass and filt),
                     rec(semiclass := semiclass));
  map := InverseGeneralMapping(IsomorphismFpSemigroup(Range(cong)));

  SetParentAttr(class, Range(cong));
  SetEquivalenceClassRelation(class, cong);
  SetRepresentative(class, Representative(semiclass) ^ map);
  return class;
end;

InstallMethod(SemigroupCongruenceByGeneratingPairs,
"for an fp monoid and a list of generating pairs",
[IsFpMonoid, IsList], RankFilter(IsList and IsEmpty),
function(M, genpairs)
  local pair, iso, semipairs, semicong, fam, cong;
  # Check that the pairs are all lists of length 2
  for pair in genpairs do
    if not IsList(pair) or Length(pair) <> 2 then
      ErrorNoReturn("Semigroups: SemigroupCongruenceByGeneratingPairs: ",
                    "usage,\n<pairs> must all be lists of length 2,");
    elif not pair[1] in M or not pair[2] in M then
      ErrorNoReturn("Semigroups: SemigroupCongruenceByGeneratingPairs: ",
                    "usage,\n<pairs> must all be lists of elements of <M>,");
    fi;
  od;

  # Make an isomorphism to an fp semigroup
  iso := IsomorphismFpSemigroup(M);
  semipairs := List(genpairs, p -> [p[1] ^ iso, p[2] ^ iso]);
  semicong := SemigroupCongruenceByGeneratingPairs(Range(iso), semipairs);

  # Create the Object
  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(M)),
                               ElementsFamily(FamilyObj(M)));
  cong := Objectify(NewType(fam, IsFpMonoidCongruence
                                 and IsSemigroupCongruence),
                    rec(semicong := semicong));
  SetSource(cong, M);
  SetRange(cong, M);
  SetGeneratingPairsOfMagmaCongruence(cong, genpairs);
  return cong;
end);

InstallMethod(LeftSemigroupCongruenceByGeneratingPairs,
"for an fp monoid and a list of generating pairs",
[IsFpMonoid, IsList], RankFilter(IsList and IsEmpty),
function(M, genpairs)
  local pair, iso, semipairs, semicong, fam, cong;
  # Check that the pairs are all lists of length 2
  for pair in genpairs do
    if not IsList(pair) or Length(pair) <> 2 then
      ErrorNoReturn("Semigroups: LeftSemigroupCongruenceByGeneratingPairs: ",
                    "usage,\n<pairs> must all be lists of length 2,");
    elif not pair[1] in M or not pair[2] in M then
      ErrorNoReturn("Semigroups: LeftSemigroupCongruenceByGeneratingPairs: ",
                    "usage,\n<pairs> must all be lists of elements of <M>,");
    fi;
  od;

  # Make an isomorphism to an fp semigroup
  iso := IsomorphismSemigroup(IsFpSemigroup, M);
  semipairs := List(genpairs, p -> [p[1] ^ iso, p[2] ^ iso]);
  semicong := LeftSemigroupCongruenceByGeneratingPairs(Range(iso), semipairs);

  # Create the Object
  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(M)),
                               ElementsFamily(FamilyObj(M)));
  cong := Objectify(NewType(fam, IsFpMonoidCongruence
                                 and IsLeftSemigroupCongruence),
                    rec(semicong := semicong));
  SetSource(cong, M);
  SetRange(cong, M);
  SetGeneratingPairsOfLeftMagmaCongruence(cong, genpairs);
  return cong;
end);

InstallMethod(RightSemigroupCongruenceByGeneratingPairs,
"for an fp monoid and a list of generating pairs",
[IsFpMonoid, IsList], RankFilter(IsList and IsEmpty),
function(M, genpairs)
  local pair, iso, semipairs, semicong, fam, cong;
  # Check that the pairs are all lists of length 2
  for pair in genpairs do
    if not IsList(pair) or Length(pair) <> 2 then
      ErrorNoReturn("Semigroups: RightSemigroupCongruenceByGeneratingPairs: ",
                    "usage,\n<pairs> must all be lists of length 2,");
    elif not pair[1] in M or not pair[2] in M then
      ErrorNoReturn("Semigroups: RightSemigroupCongruenceByGeneratingPairs: ",
                    "usage,\n<pairs> must all be lists of elements of <M>,");
    fi;
  od;

  # Make an isomorphism to an fp semigroup
  iso := IsomorphismSemigroup(IsFpSemigroup, M);
  semipairs := List(genpairs, p -> [p[1] ^ iso, p[2] ^ iso]);
  semicong := RightSemigroupCongruenceByGeneratingPairs(Range(iso), semipairs);

  # Create the Object
  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(M)),
                               ElementsFamily(FamilyObj(M)));
  cong := Objectify(NewType(fam, IsFpMonoidCongruence
                                 and IsRightSemigroupCongruence),
                    rec(semicong := semicong));
  SetSource(cong, M);
  SetRange(cong, M);
  SetGeneratingPairsOfRightMagmaCongruence(cong, genpairs);
  return cong;
end);

InstallMethod(\=,
"for two fp monoid congruences",
[IsFpMonoidCongruence, IsFpMonoidCongruence],
function(cong1, cong2)
  return IsIdenticalObj(Range(cong1), Range(cong2))
         and cong1!.semicong = cong2!.semicong;
end);

InstallMethod(JoinSemigroupCongruences,
"for two 2-sided fp monoid congruences",
[IsFpMonoidCongruence and IsSemigroupCongruence,
 IsFpMonoidCongruence and IsSemigroupCongruence],
function(cong1, cong2)
  local join, fam, map, pairs;
  if not IsIdenticalObj(Range(cong1), Range(cong2)) then
    ErrorNoReturn("Semigroups: JoinSemigroupCongruences: usage,\n",
                  "<cong1> and <cong2> must be over the same semigroup,");
  fi;
  join  := JoinSemigroupCongruences(cong1!.semicong, cong2!.semicong);
  map   := InverseGeneralMapping(IsomorphismFpSemigroup(Range(cong1)));
  pairs := List(GeneratingPairsOfSemigroupCongruence(join),
                pair -> [pair[1] ^ map, pair[2] ^ map]);

  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(Range(cong1))),
                               ElementsFamily(FamilyObj(Range(cong1))));
  join := Objectify(NewType(fam,
                            IsFpMonoidCongruence and IsSemigroupCongruence),
                    rec(semicong := join));

  SetSource(join, Source(cong1));
  SetRange(join, Range(cong1));
  SetGeneratingPairsOfMagmaCongruence(join, pairs);

  return join;
end);

InstallMethod(JoinLeftSemigroupCongruences,
"for two left fp monoid congruences",
[IsFpMonoidCongruence and IsLeftSemigroupCongruence,
 IsFpMonoidCongruence and IsLeftSemigroupCongruence],
function(cong1, cong2)
  local join, fam, map, pairs;
  if not IsIdenticalObj(Range(cong1), Range(cong2)) then
    ErrorNoReturn("Semigroups: JoinLeftSemigroupCongruences: usage,\n",
                  "<cong1> and <cong2> must be over the same semigroup,");
  fi;
  join := JoinLeftSemigroupCongruences(cong1!.semicong, cong2!.semicong);
  map   := InverseGeneralMapping(IsomorphismFpSemigroup(Range(cong1)));
  pairs := List(GeneratingPairsOfLeftSemigroupCongruence(join),
                pair -> [pair[1] ^ map, pair[2] ^ map]);

  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(Range(cong1))),
                               ElementsFamily(FamilyObj(Range(cong1))));
  join := Objectify(NewType(fam,
                            IsFpMonoidCongruence
                            and IsLeftSemigroupCongruence),
                    rec(semicong := join));

  SetSource(join, Source(cong1));
  SetRange(join, Range(cong1));
  SetGeneratingPairsOfLeftMagmaCongruence(join, pairs);

  return join;
end);

InstallMethod(JoinRightSemigroupCongruences,
"for two right fp monoid congruences",
[IsFpMonoidCongruence and IsRightSemigroupCongruence,
 IsFpMonoidCongruence and IsRightSemigroupCongruence],
function(cong1, cong2)
  local join, fam, map, pairs;

  if not IsIdenticalObj(Range(cong1), Range(cong2)) then
    ErrorNoReturn("Semigroups: JoinRightSemigroupCongruences: usage,\n",
                  "<cong1> and <cong2> must be over the same semigroup,");
  fi;

  join := JoinRightSemigroupCongruences(cong1!.semicong, cong2!.semicong);
  map   := InverseGeneralMapping(IsomorphismFpSemigroup(Range(cong1)));
  pairs := List(GeneratingPairsOfRightSemigroupCongruence(join),
                pair -> [pair[1] ^ map, pair[2] ^ map]);

  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(Range(cong1))),
                               ElementsFamily(FamilyObj(Range(cong1))));
  join := Objectify(NewType(fam,
                            IsFpMonoidCongruence
                            and IsRightSemigroupCongruence),
                    rec(semicong := join));

  SetSource(join, Source(cong1));
  SetRange(join, Range(cong1));
  SetGeneratingPairsOfRightMagmaCongruence(join, pairs);
  return join;
end);

InstallMethod(\in,
"for a multiplicative element collection and an fp monoid congruence",
[IsMultiplicativeElementCollection, IsFpMonoidCongruence],
function(pair, cong)
  local M;
  # Input checks
  M := Range(cong);
  if Size(pair) <> 2 then
    ErrorNoReturn("Semigroups: \\in (for a congruence): usage,\n",
                  "the first arg <pair> must be a list of length 2,");
  fi;
  if not (pair[1] in M and pair[2] in M) then
    ErrorNoReturn("Semigroups: \\in (for a congruence): usage,\n",
                  "elements of the first arg <pair> must be\n",
                  "in the range of the second arg <cong>,");
  fi;
  return [pair[1] ^ IsomorphismFpSemigroup(Range(cong)),
          pair[2] ^ IsomorphismFpSemigroup(Range(cong))] in cong!.semicong;
end);

InstallMethod(ImagesElm,
"for an fp monoid congruence and a multiplicative element",
[IsFpMonoidCongruence, IsMultiplicativeElement],
function(cong, elm)
  local map, inv;
  map := IsomorphismFpSemigroup(Range(cong));
  inv := InverseGeneralMapping(map);
  return List(ImagesElm(cong!.semicong, elm ^ map), x -> x ^ inv);
end);

InstallMethod(EquivalenceClasses,
"for an fp monoid congruence",
[IsFpMonoidCongruence],
function(cong)
  return List(EquivalenceClasses(cong!.semicong),
              c -> SEMIGROUPS.FpMonClassFromFpSemiClass(cong, c));
end);

InstallMethod(EquivalenceClassOfElement,
"for an fp monoid congruence and multiplicative element",
[IsFpMonoidCongruence, IsMultiplicativeElement],
function(cong, elm)
  if not elm in Range(cong) then
    ErrorNoReturn("Semigroups: EquivalenceClassOfElement: usage,\n",
                  "<elm> must be an element of the range of <cong>,");
  fi;
  return EquivalenceClassOfElementNC(cong, elm);
end);

InstallMethod(EquivalenceClassOfElementNC,
"for an fp monoid congruence and multiplicative element",
[IsFpMonoidCongruence, IsMultiplicativeElement],
function(cong, elm)
  local map, class;
  map := IsomorphismFpSemigroup(Range(cong));
  class := EquivalenceClassOfElementNC(cong!.semicong, elm ^ map);
  return SEMIGROUPS.FpMonClassFromFpSemiClass(cong, class);
end);

InstallMethod(NrEquivalenceClasses,
"for an fp monoid congruence",
[IsFpMonoidCongruence],
function(cong)
  return NrEquivalenceClasses(cong!.semicong);
end);

InstallMethod(\in,
"for a multiplicative element and an fp monoid congruence class",
[IsMultiplicativeElement, IsFpMonoidCongruenceClass],
function(elm, class)
  local map;
  map := IsomorphismFpSemigroup(Range(EquivalenceClassRelation(class)));
  return (elm ^ map in class!.semiclass);
end);

InstallMethod(Enumerator,
"for an fp monoid congruence class",
[IsFpMonoidCongruenceClass],
function(class)
  local map;
  map := IsomorphismFpSemigroup(Range(EquivalenceClassRelation(class)));
  return EnumeratorByEnumerator(class,
                                Enumerator(class!.semiclass),
                                {enum, elt} -> elt ^ InverseGeneralMapping(map),
                                {enum, elt} -> elt ^ map,
                                [],
                                rec());
end);

InstallMethod(\*,
"for two fp monoid congruence classes",
[IsFpMonoidCongruenceClass, IsFpMonoidCongruenceClass],
function(c1, c2)
  return SEMIGROUPS.FpMonClassFromFpSemiClass(EquivalenceClassRelation(c1),
                                              c1!.semiclass * c2!.semiclass);
end);

InstallMethod(Size,
"for an fp monoid congruence class",
[IsFpMonoidCongruenceClass],
function(class)
  return Size(class!.semiclass);
end);

InstallMethod(\=,
"for two fp monoid congruence classes",
[IsFpMonoidCongruenceClass, IsFpMonoidCongruenceClass],
function(c1, c2)
  return EquivalenceClassRelation(c1) = EquivalenceClassRelation(c2) and
         c1!.semiclass = c2!.semiclass;
end);

InstallMethod(IsSubrelation,
"for two fp monoid congruences",
[IsFpMonoidCongruence, IsFpMonoidCongruence],
function(cong1, cong2)
  return Range(cong1) = Range(cong2) and
         IsSubrelation(cong1!.semicong, cong2!.semicong);
end);

InstallMethod(EquivalenceRelationLookup,
"for an fp monoid congruence",
[IsFpMonoidCongruence],
function(cong)
  local iso, mon_enum, semi_enum, semilookup;
  iso        := IsomorphismFpSemigroup(Range(cong));
  mon_enum   := AsSet(Range(cong));
  semi_enum  := AsSet(Range(iso));
  semilookup := EquivalenceRelationLookup(cong!.semicong);
  return List(mon_enum, elm -> semilookup[Position(semi_enum, elm ^ iso)]);
end);

InstallMethod(EquivalenceRelationPartition,
"for an fp monoid congruence",
[IsFpMonoidCongruence],
function(cong)
  local semi_part, inv_map;
  semi_part := EquivalenceRelationPartition(cong!.semicong);
  inv_map := InverseGeneralMapping(IsomorphismFpSemigroup(Range(cong)));
  return List(semi_part, block -> List(block, elm -> elm ^ inv_map));
end);
