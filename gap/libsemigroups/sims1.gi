###########################################################################
##
##  libsemigroups/sims1.gi
##  Copyright (C) 2022                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

InstallMethod(LibsemigroupsSims1,
[IsSemigroup and CanUseFroidurePin, IsPosInt, IsListOrCollection, IsString],
function(S, n, extra, kind)
  local P, sims1, Q, r, pair;

  Assert(1, kind in ["left", "right"]);

  #TODO(Sims1) some checks on extra!

  P := libsemigroups.Presentation.make();
  for r in RulesOfSemigroup(S) do
    libsemigroups.presentation_add_rule(P, r[1] - 1, r[2] - 1);
  od;
  libsemigroups.Presentation.alphabet_from_rules(P);
  libsemigroups.Presentation.validate(P);
  libsemigroups.Presentation.contains_empty_word(P, IsMonoid(S));

  sims1 := libsemigroups.Sims1.make(kind);
  libsemigroups.Sims1.short_rules(sims1, P);

  Q := libsemigroups.Presentation.make();
  libsemigroups.Presentation.contains_empty_word(Q, IsMonoid(S));
  libsemigroups.Presentation.set_alphabet(Q,
    libsemigroups.Presentation.alphabet(P));

  for pair in extra do
    libsemigroups.presentation_add_rule(
      Q,
      MinimalFactorization(S, pair[1]) - 1,
      MinimalFactorization(S, pair[2]) - 1);
  od;
  libsemigroups.Presentation.validate(Q);
  libsemigroups.Sims1.extra(sims1, Q);
  if n > 64 then
    libsemigroups.Sims1.number_of_threads(
      sims1, libsemigroups.hardware_concurrency() - 2);
  fi;
  return sims1;
end);

InstallMethod(NumberOfRightCongruences,
"for a semigroup with CanUseFroidurePin",
[IsSemigroup and CanUseFroidurePin],
S -> NumberOfRightCongruences(S, Size(S), []));

InstallMethod(NumberOfLeftCongruences,
"for a semigroup with CanUseFroidurePin",
[IsSemigroup and CanUseFroidurePin],
S -> NumberOfLeftCongruences(S, Size(S), []));

InstallMethod(NumberOfRightCongruences,
"for a semigroup with CanUseFroidurePin and positive integer",
[IsSemigroup and CanUseFroidurePin, IsPosInt],
{S, n} -> NumberOfRightCongruences(S, n, []));

InstallMethod(NumberOfLeftCongruences,
"for a semigroup with CanUseFroidurePin and positive integer",
[IsSemigroup and CanUseFroidurePin, IsPosInt],
{S, n} -> NumberOfLeftCongruences(S, n, []));

InstallMethod(NumberOfRightCongruences,
"for CanUseFroidurePin, pos. int., list or coll.",
[IsSemigroup and CanUseFroidurePin, IsPosInt, IsListOrCollection],
function(S, n, extra)
  local sims1;

  if HasRightCongruencesOfSemigroup(S) then
    return Number(RightCongruencesOfSemigroup(S),
                  x -> NrEquivalenceClasses(x) <= n
                       and ForAll(extra, y -> y in x));
  fi;
  sims1 := LibsemigroupsSims1(S, n, extra, "right");
  return libsemigroups.Sims1.number_of_congruences(sims1, n);
end);

InstallMethod(NumberOfLeftCongruences,
"for CanUseFroidurePin, pos. int., list or coll.",
[IsSemigroup and CanUseFroidurePin, IsPosInt, IsListOrCollection],
function(S, n, extra)
  local sims1;

  if HasLeftCongruencesOfSemigroup(S) then
    return Number(LeftCongruencesOfSemigroup(S),
                  x -> NrEquivalenceClasses(x) <= n
                       and ForAll(extra, y -> y in x));
  fi;

  sims1 := LibsemigroupsSims1(S, n, extra, "left");
  return libsemigroups.Sims1.number_of_congruences(sims1, n);
end);

InstallMethod(SmallerDegreeTransformationRepresentation,
"for semigroup with CanUseFroidurePin",
[IsSemigroup and CanUseFroidurePin],
function(S)
  local map1, map2;
  map1 := IsomorphismFpSemigroup(S);
  map2 := SmallerDegreeTransformationRepresentation(Range(map1));
  return CompositionMapping(map2, map1);
end);

InstallMethod(SmallerDegreeTransformationRepresentation,
"for an fp semigroup", [IsFpSemigroup],
function(S)
  local P, ro, map, max, D, deg, imgs, pts, r, j, i;

  if not IsFinite(S) then
    TryNextMethod();
  fi;

  P := libsemigroups.Presentation.make();
  for r in RulesOfSemigroup(S) do
    libsemigroups.presentation_add_rule(P, r[1] - 1, r[2] - 1);
  od;
  libsemigroups.Presentation.alphabet_from_rules(P);
  libsemigroups.Presentation.contains_empty_word(P, true);
  libsemigroups.Presentation.validate(P);

  ro := libsemigroups.RepOrc.make();
  libsemigroups.RepOrc.short_rules(ro, P);
  libsemigroups.RepOrc.min_nodes(ro, 1);
  if HasIsomorphismTransformationSemigroup(S) then
    map := IsomorphismTransformationSemigroup(S);
    max := DegreeOfTransformationSemigroup(Range(map)) - 1;
  else
    max := Size(S);
  fi;

  libsemigroups.RepOrc.max_nodes(ro, max);
  libsemigroups.RepOrc.target_size(ro, Size(S));
  if Size(S) > 64 then
    libsemigroups.RepOrc.number_of_threads(
      ro, libsemigroups.hardware_concurrency() - 2);
  fi;

  D := libsemigroups.RepOrc.digraph(ro);
  deg := Length(D);

  if deg = 0 then
    # Should only occur if HasIsomorphismTransformationSemigroup since
    # otherwise we'll always find the right regular representation eventually.
    return IsomorphismTransformationSemigroup(S);
  fi;

  imgs := [];
  for j in [1 .. Length(GeneratorsOfSemigroup(S))] do
    pts := [1 .. deg];
    for i in pts do
      pts[i] := D[i][j];
    od;
    Add(imgs, TransformationNC(pts));
  od;
  return SemigroupIsomorphismByImagesNC(S,
                                        Semigroup(imgs),
                                        GeneratorsOfSemigroup(S),
                                        imgs);
end);

BindGlobal("NextIterator_Sims1", function(iter)
  local result;
  libsemigroups.Sims1Iterator.increment(iter!.it);
  result := libsemigroups.Sims1Iterator.deref(iter!.it);
  if IsEmpty(result) then
    return fail;
  fi;
  result := Filtered(result, x -> not IsEmpty(x));
  result := DigraphNC(result);
  SetFilterObj(result, IsWordGraph);
  return iter!.construct(result);
end);

InstallMethod(IteratorOfRightCongruences,
"for CanUseFroidurePin, pos. int., list or coll.",
[IsSemigroup and CanUseFroidurePin, IsPosInt, IsListOrCollection],
function(S, n, extra)
  local sims1, iter;

  if HasRightCongruencesOfSemigroup(S) then
    return IteratorFiniteList(Filtered(RightCongruencesOfSemigroup(S),
                    x -> NrEquivalenceClasses(x) <= n
                    and ForAll(extra, y -> y in x)));
  fi;
  sims1 := LibsemigroupsSims1(S, n, extra, "right");

  iter := rec(it := libsemigroups.Sims1.cbegin(sims1, n),
              construct := x -> RightCongruenceByWordGraph(S, x));

  iter.NextIterator := NextIterator_Sims1;
  iter.ShallowCopy := x -> rec(it := libsemigroups.Sims1.cbegin(sims1, n),
                               construct :=
                                 x -> RightCongruenceByWordGraph(S, x));
  return IteratorByNextIterator(iter);
end);

InstallMethod(IteratorOfLeftCongruences,
"for CanUseFroidurePin, pos. int., list or coll.",
[IsSemigroup and CanUseFroidurePin, IsPosInt, IsListOrCollection],
function(S, n, extra)
  local sims1, iter;
  if HasLeftCongruencesOfSemigroup(S) then
    return IteratorFiniteList(Filtered(LeftCongruencesOfSemigroup(S),
                    x -> NrEquivalenceClasses(x) <= n
                    and ForAll(extra, y -> y in x)));
  fi;

  sims1 := LibsemigroupsSims1(S, n, extra, "left");

  iter := rec(it := libsemigroups.Sims1.cbegin(sims1, n),
              construct := x -> LeftCongruenceByWordGraph(S, x));
  iter.NextIterator := NextIterator_Sims1;
  iter.ShallowCopy := x -> rec(it := libsemigroups.Sims1.cbegin(sims1, n),
                               construct :=
                                 x -> LeftCongruenceByWordGraph(S, x));
  return IteratorByNextIterator(iter);
end);

InstallMethod(IteratorOfRightCongruences,
"for CanUseFroidurePin and pos. int.",
[IsSemigroup and CanUseFroidurePin, IsPosInt],
{S, n} -> IteratorOfRightCongruences(S, n, []));

InstallMethod(IteratorOfLeftCongruences,
"for CanUseFroidurePin and pos. int.",
[IsSemigroup and CanUseFroidurePin, IsPosInt],
{S, n} -> IteratorOfLeftCongruences(S, n, []));

InstallMethod(IteratorOfRightCongruences,
"for CanUseFroidurePin",
[IsSemigroup and CanUseFroidurePin],
{S} -> IteratorOfRightCongruences(S, Size(S), []));

InstallMethod(IteratorOfLeftCongruences,
"for CanUseFroidurePin",
[IsSemigroup and CanUseFroidurePin],
{S} -> IteratorOfLeftCongruences(S, Size(S), []));
