#############################################################################
##
##  homomorph.gi
##  Copyright (C) 2022                               Artemis Konstantinidi
##                                                         Chinmaya Nagpal
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains various methods for representing homomorphisms between
# semigroups

InstallMethod(SemigroupHomomorphismByImages, "for two semigroups and two lists",
[IsSemigroup, IsSemigroup, IsList, IsList],
function(S, T, gens, imgs)
  local map, R, rel, original_gens, U;

  if not ForAll(gens, x -> x in S) then
    ErrorNoReturn("the 3rd argument (a list) must consist of elements ",
                  "of the 1st argument (a semigroup)");
  elif Semigroup(gens) <> S then
    ErrorNoReturn("the 1st argument (a semigroup) is not generated by ",
                  "the 3rd argument (a list)");
  elif not ForAll(imgs, x -> x in T) then
    ErrorNoReturn("the 4th argument (a list) must consist of elements ",
                  "of the 2nd argument (a semigroup)");
  elif Size(gens) <> Size(imgs) then
    ErrorNoReturn("the 3rd argument (a list) and the 4th argument ",
                  "(a list) are not the same size");
  fi;

  # in case of different generators, do:
  # gens -> original generators (as passed to Semigroup function)
  # imgs -> images of original generators
  original_gens := GeneratorsOfSemigroup(S);
  if original_gens <> gens then
     U := Semigroup(gens);
    imgs := List(original_gens,
      x -> EvaluateWord(imgs, Factorization(U, x)));
    gens := original_gens;
  fi;

  # maps S to a finitely presented semigroup
  map := IsomorphismFpSemigroup(S);   # S (source) -> fp semigroup (range)
  # List of relations of the above finitely presented semigroup (hence of S)
  R   := RelationsOfFpSemigroup(Range(map));

  # check that each relation is satisfied by the elements imgs
  for rel in R do
    rel := List(rel, x -> SEMIGROUPS.ExtRepObjToWord(ExtRepOfObj(x)));
    if EvaluateWord(imgs, rel[1]) <> EvaluateWord(imgs, rel[2]) then
      return fail;
    fi;
  od;

  return SemigroupHomomorphismByImages_NC(S, T, gens, imgs);
end);

InstallMethod(SemigroupHomomorphismByImages,
"for two transformation semigroups and two transformation collections",
[IsTransformationSemigroup and IsActingSemigroup,
    IsTransformationSemigroup and IsActingSemigroup,
    IsTransformationCollection and IsList,
    IsTransformationCollection and IsList],
function(S, T, gens, imgs)
  local K, SxT, embS, embT, S1, T1, i, original_gens, U;

  if not ForAll(gens, x -> x in S) then
    ErrorNoReturn("the 3rd argument (a list) must consist of elements ",
                  "of the 1st argument (a semigroup)");
  elif Semigroup(gens) <> S then
    ErrorNoReturn("the 1st argument (a semigroup) is not generated by ",
                  "the 3rd argument (a list)");
  elif not ForAll(imgs, x -> x in T) then
    ErrorNoReturn("the 4th argument (a list) must consist of elements ",
                  "of the 2nd argument (a semigroup)");
  elif Size(gens) <> Size(imgs) then
    ErrorNoReturn("the 3rd argument (a list) and the 4th argument ",
                  "(a list) are not the same size");
  fi;

  # in case of different generators, do:
  # gens -> original generators (as passed to Semigroup function)
  # imgs -> images of original generators
  original_gens := GeneratorsOfSemigroup(S);
  if original_gens <> gens then
    U := Semigroup(gens, rec(acting := true));
    imgs := List(original_gens,
      x -> EvaluateWord(imgs, Factorization(U, x)));
    gens := original_gens;
  fi;

  if not IsMonoidAsSemigroup(S) then
    S1 := Monoid(S);
  else
    S1 := S;
  fi;

  if not IsMonoidAsSemigroup(T) then
    T1 := Monoid(T);
  else
    T1 := T;
  fi;

  SxT  := DirectProduct(S1, T1);
  embS := Embedding(SxT, 1);
  embT := Embedding(SxT, 2);
  K    := [];

  for i in [1 .. Size(gens)] do
    Add(K, gens[i] ^ embS * imgs[i] ^ embT);
  od;
  K := Semigroup(K, rec(acting := true));

  # todo: stop this loop as soon as K exceeds S in size:
  if Size(K) <> Size(S) then
    return fail;
  else
    return SemigroupHomomorphismByImages_NC(S, T, gens, imgs);
  fi;
end);

InstallMethod(SemigroupHomomorphismByImages, "for two semigroups and one list",
[IsSemigroup, IsSemigroup, IsList],
function(S, T, imgs)
  local gens;
  gens := GeneratorsOfSemigroup(S);
  return SemigroupHomomorphismByImages(S, T, gens, imgs);
end);

InstallMethod(SemigroupHomomorphismByImages, "for two semigroups",
[IsSemigroup, IsSemigroup],
function(S, T)
  local gens, imgs;
  gens := GeneratorsOfSemigroup(S);
  imgs := GeneratorsOfSemigroup(T);
  return SemigroupHomomorphismByImages(S, T, gens, imgs);
end);

InstallMethod(SemigroupHomomorphismByImages, "for a semigroup and two lists",
[IsSemigroup, IsList, IsList],
function(S, gens, imgs)
  local T;
  T := Semigroup(imgs);
  return SemigroupHomomorphismByImages(S, T, gens, imgs);
end);

InstallMethod(SemigroupIsomorphismByImages, "for two semigroup and two lists",
[IsSemigroup, IsSemigroup, IsList, IsList],
function(S, T, gens, imgs)
  local hom;
  hom := SemigroupHomomorphismByImages(S, T, gens, imgs);
  if IsBijective(hom) then
    return hom;
  fi;
  return fail;
end);

InstallMethod(SemigroupIsomorphismByImagesNC, "for two semigroup and two lists",
[IsSemigroup, IsSemigroup, IsList, IsList],
function(S, T, gens, imgs)
  local iso;
  iso := Objectify(NewType(GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                                               ElementsFamily(FamilyObj(T))),
                         IsSemigroupHomomorphismByImages and IsBijective),
                         rec());
  SetSource(iso, S);
  SetRange(iso, T);
  SetMappingGeneratorsImages(iso, [Immutable(gens), Immutable(imgs)]);
  return iso;
end);

InstallMethod(SemigroupIsomorphismByImages, "for two semigroups and one list",
[IsSemigroup, IsSemigroup, IsList],
function(S, T, imgs)
  local gens;
  gens := GeneratorsOfSemigroup(S);
  return SemigroupIsomorphismByImages(S, T, gens, imgs);
end);

InstallMethod(SemigroupIsomorphismByImages, "for two semigroups",
[IsSemigroup, IsSemigroup],
function(S, T)
  local gens, imgs;
  gens := GeneratorsOfSemigroup(S);
  imgs := GeneratorsOfSemigroup(T);
  return SemigroupIsomorphismByImages(S, T, gens, imgs);
end);

InstallMethod(SemigroupIsomorphismByImages, "for a semigroup and two lists",
[IsSemigroup, IsList, IsList],
function(S, gens, imgs)
  local T;
  T := Semigroup(imgs);
  return SemigroupIsomorphismByImages(S, T, gens, imgs);
end);

InstallMethod(SemigroupHomomorphismByImages_NC,
"for two semigroups and two lists",
[IsSemigroup, IsSemigroup, IsList, IsList],
function(S, T, gens, imgs)
  local hom;
  # if HasGeneratorsOfGroup(Gt;)
  #    and IsIdenticalObj(GeneratorsOfGroup(G),mapi[1]) then
  #   Append(obj_args, [PreImagesRange, G]);
  #   filter := filter and IsTotal and HasPreImagesRange;
  # fi;
  #
  # if HasGeneratorsOfGroup(H)
  #    and IsIdenticalObj(GeneratorsOfGroup(H),mapi[2]) then
  #   Append(obj_args, [ImagesSource, H]);
  #   filter := filter and IsSurjective and HasImagesSource;
  # fi;

  hom := Objectify(NewType(GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                                                 ElementsFamily(FamilyObj(T))),
                           IsSemigroupHomomorphismByImages), rec());
  SetSource(hom, S);
  SetRange(hom, T);
  SetMappingGeneratorsImages(hom, [Immutable(gens), Immutable(imgs)]);

  return hom;
end);

InstallMethod(SemigroupHomomorphismByFunction,
"for two semigroups and a function",
[IsSemigroup, IsSemigroup, IsFunction],
function(S, T, f)
  local hom;
  hom := Objectify(NewType(GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                                                 ElementsFamily(FamilyObj(T))),
                           IsSemigroupHomomorphismByFunction), rec(fun := f));
  SetSource(hom, S);
  SetRange(hom, T);
  return hom;
end);

InstallMethod(SemigroupIsomorphismByFunction,
"for two semigroups and two functions",
[IsSemigroup, IsSemigroup, IsFunction, IsFunction],
function(S, T, f, g)
  local hom;
  hom := SemigroupHomomorphismByFunction(S, T, f);
  if IsBijective(hom) then
    return SemigroupIsomorphismByFunctionNC(S, T, f, g);
  else
    return fail;
  fi;
end);

InstallMethod(SemigroupIsomorphismByFunctionNC,
"for two semigroups and two functions",
[IsSemigroup, IsSemigroup, IsFunction, IsFunction],
function(S, T, f, g)
  local iso;
  iso := Objectify(NewType(GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                                                 ElementsFamily(FamilyObj(T))),
                           IsSemigroupIsomorphismByFunction),
                           rec(fun    := f,
                               invFun := g));
  SetSource(iso, S);
  SetRange(iso, T);
  return iso;
end);

InstallMethod(InverseGeneralMapping,
"for a semigroup isomorphism by function",
[IsSemigroupHomomorphismByFunction and IsBijective],
function(map)
  local inv;
  inv := SemigroupIsomorphismByFunctionNC(Range(map),
                                          Source(map),
                                          map!.invFun,
                                          map!.fun);
  TransferMappingPropertiesToInverse(map, inv);
  return inv;
end);

# methods for converting between SHBI and SHBF
InstallMethod(AsSemigroupHomomorphismByImages,
"for a semigroup homomorphism by function",
[IsSemigroupHomomorphismByFunction],
function(hom)
  local S, T, gens, imgs;
  S    := Source(hom);
  T    := Range(hom);
  gens := GeneratorsOfSemigroup(S);
  imgs := List(gens, x -> x ^ hom);
  return SemigroupHomomorphismByImages(S, T, gens, imgs);
end);

InstallMethod(AsSemigroupHomomorphismByFunction,
"for a semigroup homomorphism by images",
[IsSemigroupHomomorphismByImages],
hom -> SemigroupHomomorphismByFunction(Source(hom),
                      Range(hom), x -> ImageElm(hom, x)));

InstallMethod(AsSemigroupIsomorphismByFunction,
"for a semigroup homomorphism by images",
[IsSemigroupHomomorphismByImages],
hom -> SemigroupIsomorphismByFunction(Source(hom),
                      Range(hom), x -> ImageElm(hom, x),
                      y -> PreImages(hom, y)));

# Methods for SHBI/SIBI/SHBF
InstallMethod(IsSurjective, "for a semigroup homomorphism",
  [IsSemigroupHomomorphismByImagesOrFunction],
function(hom)
  return Size(ImagesSource(hom)) = Size(Range(hom));
end);

InstallMethod(IsInjective, "for a semigroup homomorphism",
  [IsSemigroupHomomorphismByImagesOrFunction],
function(hom)
  return Size(Source(hom)) = Size(ImagesSource(hom));
end);

InstallMethod(ImagesSet, "for a semigroup homom. and list of elements",
    [IsSemigroupHomomorphismByImagesOrFunction, IsList],
    {hom, elms} -> List(elms, x -> ImageElm(hom, x)));

InstallMethod(ImageElm, "for a semigroup homom. by images and element",
[IsSemigroupHomomorphismByImages, IsMultiplicativeElement],
function(hom, x)
  if not x in Source(hom) then
    ErrorNoReturn("the 2nd argument (a mult. elt.) is not an element ",
    "of the source of the 1st argument (semigroup homom. by images)");
  fi;
  return EvaluateWord(MappingGeneratorsImages(hom)[2],
                      Factorization(Source(hom), x));
end);

InstallMethod(ImagesSource, "for SHBI",
    [IsSemigroupHomomorphismByImages],
    hom -> Semigroup(MappingGeneratorsImages(hom)[2]));

InstallMethod(PreImagesRepresentative,
"for a semigroup homom. by images and an element in the range",
[IsSemigroupHomomorphismByImages, IsMultiplicativeElement],
function(hom, x)
  if not x in Range(hom) then
    ErrorNoReturn("the 2nd argument is not an element of the range of the ",
    "1st argument (semigroup homom. by images)");
  elif not x in ImagesSource(hom) then
    return fail;
  fi;
  return EvaluateWord(MappingGeneratorsImages(hom)[1],
                      Factorization(ImagesSource(hom), x));
end);

InstallMethod(ImagesElm, "for a semigroup homom. by images and an element",
    [IsSemigroupHomomorphismByImages, IsMultiplicativeElement],
    {hom, x} -> [ImageElm(hom, x)]);

InstallMethod(PreImagesElm,
"for a semigroup homom. by images and an element in the range",
[IsSemigroupHomomorphismByImages, IsMultiplicativeElement],
function(hom, x)
  local preim, y;
  if not x in Range(hom) then
    ErrorNoReturn("the 2nd argument is not an element of the range of the ",
                  "1st argument (semigroup homom. by images)");
  elif not x in ImagesSource(hom) then
    ErrorNoReturn("the 2nd argument is not mapped to by the 1st argument ",
                  "(semigroup homom. by images)");
  fi;
  preim := [];
  for y in Source(hom) do
    if ImageElm(hom, y) = x then
      Add(preim, y);
    fi;
  od;
  return preim;
end);

InstallMethod(PreImagesSet,
"for a semigroup homom. by images and a set of elements in the range",
[IsSemigroupHomomorphismByImages, IsList],
function(hom, elms)
  local y, preim;
  if not IsSubsetSet(AsList(Range(hom)), elms) then
    ErrorNoReturn("the 2nd argument is not a subset of the range of the ",
                  "1st argument (semigroup homom. by images)");
  elif not IsSubsetSet(AsList(ImagesSource(hom)), elms) then
    ErrorNoReturn("the 2nd argument is not a subset of the image of the ",
                  "source of the 1st argument (semigroup homom. by images)");
  fi;
  preim := [];
  for y in elms do
    Append(preim, PreImagesElm(hom, y));
  od;
  return preim;
end);

InstallMethod(KernelOfSemigroupHomomorphism, "for a semigroup homomorphism",
[IsSemigroupHomomorphismByImagesOrFunction],
function(hom)
  local S, cong, enum, x, y, pairs, i, j;

  S := Source(hom);
  if IsBijective(hom) then
    return SemigroupCongruence(S, []);
  elif Size(ImagesSource(hom)) = 1 then
    return UniversalSemigroupCongruence(S);
  fi;

  cong := SemigroupCongruence(S, []);
  enum := EnumeratorCanonical(S);
  for i in [1 .. Size(S) - 1] do
    x := enum[i];
    for j in [i + 1 .. Size(S)] do
      y := enum[j];
      if x ^ hom = y ^ hom then
        if not [x, y] in cong then
          pairs := ShallowCopy(GeneratingPairsOfSemigroupCongruence(cong));
          Add(pairs, [x, y]);
          cong := SemigroupCongruence(S, pairs);
          if NrEquivalenceClasses(cong) = Size(ImagesSource(hom)) then
            return cong;
          fi;
        fi;
      fi;
    od;
  od;
  return cong;
end);

InstallMethod(String, "for a semigroup homom. by images",
  [IsSemigroupHomomorphismByImages],
function(hom)
  local mapi;
  mapi := MappingGeneratorsImages(hom);
  return Concatenation("SemigroupHomomorphismByImages( ",
          String(Source(hom)), ", ", String(Range(hom)), ", ",
          String(mapi[1]), ", ", String(mapi[2]), " )");
end);

InstallMethod(PrintObj, "for a semigroup homom. by images",
[IsSemigroupHomomorphismByImages],
function(hom)
  Print(String(hom));
  return;
end);

InstallMethod(String, "for a semigroup isom. by images",
[IsSemigroupHomomorphismByImages and IsBijective],
function(iso)
  local mapi;
  mapi := MappingGeneratorsImages(iso);
  return Concatenation("SemigroupIsomorphismByImages( ",
          String(Source(iso)), ", ", String(Range(iso)), ", ",
          String(mapi[1]), ", ", String(mapi[2]), " )");
end);

InstallMethod(\=, "compare homom. by images", IsIdenticalObj,
[IsSemigroupHomomorphismByImages, IsSemigroupHomomorphismByImages],
function(hom1, hom2)
  local i;
  if Source(hom1) <> Source(hom2)
      or Range(hom1) <> Range(hom2)
      or PreImagesRange(hom1) <> PreImagesRange(hom2)
      or ImagesSource(hom1) <> ImagesSource(hom2) then
    return false;
  fi;
  hom1 := MappingGeneratorsImages(hom1);
  return hom1[2] = List(hom1[1], i -> ImageElm(hom2, i));
end);

InstallMethod(ViewObj, "for SHBI/SHBF",
[IsSemigroupHomomorphismByImagesOrFunction],
2,  # to beat method for mapping by function with inverse
function(hom)
  if UserPreference("semigroups", "HomomorphismView") <> "semigroups-pkg" then
    TryNextMethod();
  fi;
  Print("\>");
  ViewObj(Source(hom));
  Print("\< \>->\< \>");
  ViewObj(Range(hom));
  Print("\<");
end);

InstallMethod(String, "for a semigroup homom. by function",
  [IsSemigroupHomomorphismByFunction],
function(hom)
  if UserPreference("semigroups", "HomomorphismView") <> "semigroups-pkg" then
    TryNextMethod();
  fi;
  return Concatenation("SemigroupHomomorphismByFunction( ",
          String(Source(hom)), ", ", String(Range(hom)), ", ",
          String(hom!.fun), " )");
end);

InstallMethod(PrintObj, "for a semigroup homom. by function",
  [IsSemigroupHomomorphismByFunction],
function(hom)
  if UserPreference("semigroups", "HomomorphismView") <> "semigroups-pkg" then
    TryNextMethod();
  fi;
  Print(String(hom));
  return;
end);

InstallMethod(String, "for a semigroup isom. by function",
  [IsSemigroupIsomorphismByFunction],
function(iso)
  if UserPreference("semigroups", "HomomorphismView") <> "semigroups-pkg" then
    TryNextMethod();
  fi;
  return Concatenation("SemigroupIsomorphismByFunction( ",
          String(Source(iso)), ", ", String(Range(iso)), ", ",
          String(iso!.fun), ", ",
          String(iso!.invFun), " )");
end);

InstallMethod(PrintObj, "for a semigroup isom. by function",
  [IsSemigroupIsomorphismByFunction],
function(iso)
  if UserPreference("semigroups", "HomomorphismView") <> "semigroups-pkg" then
    TryNextMethod();
  fi;
  Print(String(iso));
  return;
end);
