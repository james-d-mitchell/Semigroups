############################################################################
##
##  congruences/conglatt.gi
##  Copyright (C) 2016-2022                               Michael C. Young
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
## This file contains functions for a poset of congruences.
##
## When the congruences of a semigroup are computed, they form a lattice with
## respect to containment.  The information about the congruences' positions in
## this lattice may be stored in an IsCongruencePoset object (a component object
## based on a record) and can be retrieved from this object using the methods in
## this file.
##
## The list of congruences in the poset is stored as an attribute
## CongruencesOfPoset.  The partial order of the poset is stored as a digraph,
## where an edge (i,j) is present if and only if congruence i is a subrelation
## of congruence j.  When a congruence poset is displayed, it appears to the
## user as the list of out-neighbours of that digraph.
##

#############################################################################
## The main three functions
#############################################################################

SEMIGROUPS.PrincipalXCongruencePosetNC :=
  function(S, pairs, SemigroupXCongruence)
    local total, congs, nrcongs, children, parents, last_collected, nr,
    badcong, newchildren, newparents, newcong, pair1, poset, pair, i, c, p;

  # Get all the unique principal congs
  if IsList(pairs) then
    total := Length(pairs);
  else
    total := Binomial(Size(S), 2);
  fi;
  Info(InfoSemigroups, 1, "Finding principal congruences . . .");
  congs := [];      # List of all congs found so far
  nrcongs := 0;     # Number of congs found so far
  children := [];   # List of lists of children
  parents := [];    # List of lists of parents
  last_collected := 0;
  nr := 0;
  for pair in pairs do
    if pair[1] = pair[2] then
      continue;
    fi;
    badcong := false;
    newchildren := [];  # Children of newcong
    newparents := [];   # Parents of newcong
    newcong := SemigroupXCongruence(S, pair);
    for i in [1 .. Length(congs)] do
      pairs := GeneratingPairsOfLeftRightOrTwoSidedCongruence(congs[i]);
      if not IsEmpty(pairs) then
        pair1 := pairs[1];
        if CongruenceTestMembershipNC(congs[i], pair[1], pair[2]) then
          if CongruenceTestMembershipNC(newcong, pair1[1], pair1[2]) then
            # This is not a new cong - drop it!
            badcong := true;
            break;
          else
            Add(newparents, i);
          fi;
        elif CongruenceTestMembershipNC(newcong, pair1[1], pair1[2]) then
          Add(newchildren, i);
        fi;
      fi;
    od;
    nr := nr + 1;
    if nr > last_collected + 1999 then
      Info(InfoSemigroups,
           1,
           StringFormatted("Pair {} of {}: {} congruences so far",
                           nr,
                           total,
                           nrcongs));
      last_collected := nr;
      GASMAN("collect");
    fi;
    if not badcong then
      nrcongs := nrcongs + 1;
      congs[nrcongs] := newcong;
      for c in newchildren do
        Add(parents[c], nrcongs);
      od;
      for p in newparents do
        Add(children[p], nrcongs);
      od;
      Add(newchildren, nrcongs);  # Include loops (reflexive)
      Add(newparents, nrcongs);
      children[nrcongs] := newchildren;
      parents[nrcongs] := newparents;
    fi;
  od;

  # We are done: make the object and return
  poset := Digraph(parents);
  SetInNeighbours(poset, children);
  SetCongruencesOfPoset(poset, congs);
  SetDigraphVertexLabels(poset, congs);
  SetUnderlyingSemigroupOfCongruencePoset(poset, S);
  SetFilterObj(poset, IsCongruencePoset);
  return poset;
end;

InstallMethod(PosetOfCongruences, "for a list or collection",
[IsListOrCollection],
function(coll)
  local congs, nrcongs, children, parents, i, ignore, j, poset;
  congs := AsList(coll);
  nrcongs := Length(congs);

  # Setup children and parents lists
  children := [];
  parents := [];
  for i in [1 .. nrcongs] do
    children[i] := Set([i]);
    parents[i] := Set([i]);
  od;

  # Find children of each cong in turn
  for i in [1 .. nrcongs] do
    # Ignore known parents
    ignore := BlistList([1 .. nrcongs], [parents[i]]);
    for j in [1 .. nrcongs] do
      if not ignore[j] and IsSubrelation(congs[i], congs[j]) then
        AddSet(children[i], j);
        AddSet(parents[j], i);
      fi;
    od;
  od;

  # We are done: make the object and return
  poset := Digraph(parents);
  SetInNeighbours(poset, children);
  SetCongruencesOfPoset(poset, congs);
  SetDigraphVertexLabels(poset, congs);
  if nrcongs > 0 then
    SetUnderlyingSemigroupOfCongruencePoset(poset, Range(congs[1]));
  fi;
  SetFilterObj(poset, IsCongruencePoset);
  return poset;
end);

SEMIGROUPS.AddTrivialCongruence := function(poset, SemigroupXCongruence)
  local S, children, parents, congs, nrcongs, i;
  # Extract the info
  S := UnderlyingSemigroupOfCongruencePoset(poset);
  children := InNeighboursMutableCopy(poset);
  parents := OutNeighboursMutableCopy(poset);
  congs := ShallowCopy(CongruencesOfPoset(poset));

  # Add the trivial congruence
  nrcongs := Length(congs) + 1;
  Add(congs, SemigroupXCongruence(S, []), 1);
  children := Concatenation([[]], children + 1);
  parents := Concatenation([[1 .. nrcongs]], parents + 1);
  for i in [1 .. nrcongs] do
    Add(children[i], 1, 1);
  od;

  # Make the object and return
  poset := Digraph(parents);
  SetInNeighbours(poset, children);
  SetCongruencesOfPoset(poset, congs);
  SetDigraphVertexLabels(poset, congs);
  SetUnderlyingSemigroupOfCongruencePoset(poset, S);
  SetFilterObj(poset, IsCongruencePoset);
  return poset;
end;

InstallMethod(JoinSemilatticeOfCongruences,
"for a congruence poset and a function",
[IsCongruencePoset, IsFunction],
function(poset, JoinXCongruences)
  local children, parents, congs, princ_congs, nrcongs, S, length, found,
  start, newcong, badcong, newchildren, newparents, i, j, k, c, p;

  # Trivial case
  if DigraphNrVertices(poset) = 0 then
    return poset;
  fi;

  # Extract the info
  children := InNeighboursMutableCopy(poset);
  parents := OutNeighboursMutableCopy(poset);
  congs := ShallowCopy(CongruencesOfPoset(poset));
  # FIXME this has the built in assumption that all the congruences in poset
  # are principal
  princ_congs := ShallowCopy(congs);
  nrcongs := Length(congs);
  S := UnderlyingSemigroupOfCongruencePoset(poset);

  # Take all the joins
  Info(InfoSemigroups, 1, "Finding joins of congruences . . .");
  length := 0;
  found := true;
  while found do
    # There are new congs to try joining
    start := length + 1;      # New congs start here
    found := false;           # Have we found any more congs on this sweep?
    length := Length(congs);  # Remember starting position for next sweep

    for i in [start .. Length(congs)] do      # for each new cong
      for j in [1 .. Length(princ_congs)] do  # for each 1-generated cong
        newcong := JoinXCongruences(congs[i], princ_congs[j]);
        badcong := false;   # Is newcong the same as another cong?
        newchildren := [];  # Children of newcong
        newparents := [];   # Parents of newcong
        for k in [1 .. Length(congs)] do
          if IsSubrelation(congs[k], newcong) then
            if IsSubrelation(newcong, congs[k]) then
              # This is the same as an old cong - discard it!
              badcong := true;
              break;
            else
              Add(newparents, k);
            fi;
          elif IsSubrelation(newcong, congs[k]) then
            Add(newchildren, k);
          fi;
        od;
        if not badcong then
          nrcongs := nrcongs + 1;
          congs[nrcongs] := newcong;
          for c in newchildren do
            Add(parents[c], nrcongs);
          od;
          for p in newparents do
            Add(children[p], nrcongs);
          od;
          Add(newchildren, nrcongs);  # Include loops (reflexive)
          Add(newparents, nrcongs);
          children[nrcongs] := newchildren;
          parents[nrcongs] := newparents;
          found := true;
        fi;
      od;
      Info(InfoSemigroups, 2, "Processed cong ", i, " of ", Length(congs),
           " (", Length(congs) - i, " remaining)");
    od;
  od;

  # We are done: make the object and return
  princ_congs := poset;
  poset := Digraph(parents);
  SetInNeighbours(poset, children);
  SetCongruencesOfPoset(poset, congs);
  SetDigraphVertexLabels(poset, congs);
  SetUnderlyingSemigroupOfCongruencePoset(poset, S);
  SetFilterObj(poset, IsCongruencePoset);
  SetPosetOfPrincipalCongruences(poset, princ_congs);
  return poset;
end);

BindGlobal("_CheckCongruenceLatticeArgs",
function(S, obj)
  if not (IsFinite(S) and CanUseFroidurePin(S)) then
    ErrorNoReturn("the 1st argument (a semigroup) must be finite and have ",
                  "CanUseFroidurePin");
  elif IsIterator(obj) then
    return;
  elif not (IsEmpty(obj) or IsMultiplicativeElementCollColl(obj)) then
    ErrorNoReturn("the 2nd argument (a list or collection) must be ",
                  "empty or a mult. elt. coll. coll.");
  elif not ForAll(obj, x -> Size(x) = 2)
      or not ForAll(obj, x -> x[1] in S and x[2] in S)  then
    ErrorNoReturn("the 2nd argument (a list) must consist of ",
                  "pairs of the 1st argument (a semigroup)");
  fi;
end);

########################################################################
# GeneratingPairsOfPrincipalCongruences
########################################################################

InstallMethod(GeneratingPairsOfPrincipalCongruences, "for a semigroup",
[IsSemigroup],
function(S)
  if not (IsFinite(S) and CanUseFroidurePin(S)) then
    ErrorNoReturn("the argument (a semigroup) must be finite and have ",
                  "CanUseFroidurePin");
  fi;
  return Combinations(AsList(S), 2);
  # return IteratorOfCombinations(AsList(S), 2);
end);

InstallMethod(GeneratingPairsOfPrincipalLeftCongruences,
"for an acting semigroup", [IsSemigroup],
function(S)
  if not (IsFinite(S) and CanUseFroidurePin(S)) then
    ErrorNoReturn("the argument (a semigroup) must be finite and have ",
                  "CanUseFroidurePin");
  fi;
  return Combinations(AsList(S), 2);
  # return IteratorOfCombinations(AsList(S), 2);
end);

InstallMethod(GeneratingPairsOfPrincipalRightCongruences,
"for an acting semigroup", [IsSemigroup],
GeneratingPairsOfPrincipalCongruences);

InstallMethod(GeneratingPairsOfPrincipalCongruences, "for an acting semigroup",
[IsActingSemigroup],
function(S)
  local M, MxM, map1, map2, Delta, pairs;
  if not (IsFinite(S) and CanUseFroidurePin(S)) then
    ErrorNoReturn("the argument (a semigroup) must be finite and have ",
                  "CanUseFroidurePin");
  elif not IsMonoid(S) and not IsMonoidAsSemigroup(S) then
    M := Monoid(S, rec(acting := true));
  else
    M := S;
  fi;

  MxM   := DirectProduct(M, M);
  SetFilterObj(MxM, IsActingSemigroup);
  map1  := Embedding(MxM, 1);
  map2  := Embedding(MxM, 2);

  Delta := Set(GeneratorsOfSemigroup(S), x -> x ^ map1 * x ^ map2);
  pairs := RelativeDClassReps(MxM, Semigroup(Delta, rec(acting := true)));
  map1  := Projection(MxM, 1);
  map2  := Projection(MxM, 2);
  pairs := Set(pairs, x -> AsSortedList([x ^ map1, x ^ map2]));
  return Filtered(pairs, x -> x[1] in S and x[2] in S);
end);

InstallMethod(GeneratingPairsOfPrincipalRightCongruences,
"for an acting semigroup",
[IsActingSemigroup],
function(S)
  local M, MxM, map1, map2, Delta, pairs;

  if not (IsFinite(S) and CanUseFroidurePin(S)) then
    ErrorNoReturn("the argument (a semigroup) must be finite and have ",
                  "CanUseFroidurePin");
  elif not IsMonoid(S) and not IsMonoidAsSemigroup(S) then
    M := Monoid(S);
  else
    M := S;
  fi;

  MxM   := DirectProduct(M, M);
  map1  := Embedding(MxM, 1);
  map2  := Embedding(MxM, 2);

  Delta := Set(GeneratorsOfSemigroup(S), x -> x ^ map1 * x ^ map2);
  pairs := RelativeRClassReps(MxM, Semigroup(Delta));
  map1  := Projection(MxM, 1);
  map2  := Projection(MxM, 2);
  pairs := Set(pairs, x -> AsSortedList([x ^ map1, x ^ map2]));
  return Filtered(pairs, x -> x[1] in S and x[2] in S);
end);

########################################################################
# PosetOfPrincipalRight/LeftCongruences
########################################################################

InstallMethod(PosetOfPrincipalCongruences, "for a semigroup", [IsSemigroup],
function(S)
  local pairs;
  if HasLatticeOfCongruences(S) then
    return PosetOfPrincipalCongruences(LatticeOfCongruences(S));
  fi;
  pairs := GeneratingPairsOfPrincipalCongruences(S);
  return SEMIGROUPS.PrincipalXCongruencePosetNC(S,
                                                pairs,
                                                SemigroupCongruence);
end);

InstallMethod(PosetOfPrincipalCongruences,
"for a semigroup and list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  _CheckCongruenceLatticeArgs(S, pairs);
  return SEMIGROUPS.PrincipalXCongruencePosetNC(S,
                                                pairs,
                                                SemigroupCongruence);
end);

InstallMethod(PosetOfPrincipalRightCongruences, "for a semigroup",
[IsSemigroup],
function(S)
  local pairs;
  if HasLatticeOfRightCongruences(S) then
    return PosetOfPrincipalRightCongruences(LatticeOfRightCongruences(S));
  fi;
  pairs := GeneratingPairsOfPrincipalRightCongruences(S);
  return SEMIGROUPS.PrincipalXCongruencePosetNC(S,
                                                pairs,
                                                RightSemigroupCongruence);
end);

InstallMethod(PosetOfPrincipalRightCongruences,
"for a semigroup and list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  _CheckCongruenceLatticeArgs(S, pairs);
  return SEMIGROUPS.PrincipalXCongruencePosetNC(S,
                                                pairs,
                                                RightSemigroupCongruence);
end);

InstallMethod(PosetOfPrincipalLeftCongruences, "for a semigroup",
[IsSemigroup],
function(S)
  local pairs;
  if HasLatticeOfLeftCongruences(S) then
    return PosetOfPrincipalLeftCongruences(LatticeOfLeftCongruences(S));
  fi;
  pairs := GeneratingPairsOfPrincipalLeftCongruences(S);
  return SEMIGROUPS.PrincipalXCongruencePosetNC(S,
                                                pairs,
                                                LeftSemigroupCongruence);
end);

InstallMethod(PosetOfPrincipalLeftCongruences,
"for a semigroup and list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  _CheckCongruenceLatticeArgs(S, pairs);
  return SEMIGROUPS.PrincipalXCongruencePosetNC(S,
                                                pairs,
                                                LeftSemigroupCongruence);
end);

#############################################################################
## LatticeOfCongruences
#############################################################################

InstallMethod(LatticeOfCongruencesNC,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  local poset;
  poset := PosetOfPrincipalCongruences(S, pairs);
  poset := JoinSemilatticeOfCongruences(poset, JoinSemigroupCongruences);
  return SEMIGROUPS.AddTrivialCongruence(poset, SemigroupCongruence);
end);

InstallMethod(LatticeOfCongruences,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  _CheckCongruenceLatticeArgs(S, pairs);
  return LatticeOfCongruencesNC(S, pairs);
end);

InstallMethod(LatticeOfCongruences, "for a semigroup", [IsSemigroup],
function(S)
  return LatticeOfCongruencesNC(S, GeneratingPairsOfPrincipalCongruences(S));
end);

InstallMethod(LatticeOfRightCongruencesNC,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  local poset;
  poset := PosetOfPrincipalRightCongruences(S, pairs);
  poset := JoinSemilatticeOfCongruences(poset, JoinRightSemigroupCongruences);
  return SEMIGROUPS.AddTrivialCongruence(poset, SemigroupCongruence);
end);

InstallMethod(LatticeOfRightCongruences,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  _CheckCongruenceLatticeArgs(S, pairs);
  return LatticeOfRightCongruencesNC(S, pairs);
end);

InstallMethod(LatticeOfRightCongruences, "for a semigroup", [IsSemigroup],
function(S)
  return LatticeOfRightCongruencesNC(S,
           GeneratingPairsOfPrincipalRightCongruences(S));
end);

InstallMethod(LatticeOfLeftCongruencesNC,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  local poset;
  poset := PosetOfPrincipalLeftCongruences(S, pairs);
  poset := JoinSemilatticeOfCongruences(poset, JoinLeftSemigroupCongruences);
  return SEMIGROUPS.AddTrivialCongruence(poset, SemigroupCongruence);
end);

InstallMethod(LatticeOfLeftCongruences,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  _CheckCongruenceLatticeArgs(S, pairs);
  return LatticeOfLeftCongruencesNC(S, pairs);
end);

InstallMethod(LatticeOfLeftCongruences, "for a semigroup", [IsSemigroup],
function(S)
  return LatticeOfLeftCongruencesNC(S,
           GeneratingPairsOfPrincipalLeftCongruences(S));
end);

########################################################################
# Left/Right/CongruencesOfSemigroup
########################################################################

InstallMethod(LeftCongruencesOfSemigroup,
"for a semigroup", [IsSemigroup],
S -> CongruencesOfPoset(LatticeOfLeftCongruences(S)));

InstallMethod(RightCongruencesOfSemigroup,
"for a semigroup", [IsSemigroup],
S -> CongruencesOfPoset(LatticeOfRightCongruences(S)));

InstallMethod(CongruencesOfSemigroup,
"for a semigroup", [IsSemigroup],
S -> CongruencesOfPoset(LatticeOfCongruences(S)));

########################################################################
# Principal congruences
########################################################################

InstallMethod(PrincipalLeftCongruencesOfSemigroup,
"for a semigroup", [IsSemigroup],
S -> CongruencesOfPoset(PosetOfPrincipalLeftCongruences(S)));

InstallMethod(PrincipalRightCongruencesOfSemigroup,
"for a semigroup", [IsSemigroup],
S -> CongruencesOfPoset(PosetOfPrincipalRightCongruences(S)));

InstallMethod(PrincipalCongruencesOfSemigroup,
"for a semigroup", [IsSemigroup],
S -> CongruencesOfPoset(PosetOfPrincipalCongruences(S)));

InstallMethod(PrincipalLeftCongruencesOfSemigroup,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, restriction)
  return CongruencesOfPoset(PosetOfPrincipalLeftCongruences(S, restriction));
end);

InstallMethod(PrincipalRightCongruencesOfSemigroup,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, restriction)
  return CongruencesOfPoset(PosetOfPrincipalRightCongruences(S, restriction));
end);

InstallMethod(PrincipalCongruencesOfSemigroup,
"for a semigroup and a list or collection",
[IsSemigroup, IsListOrCollection],
function(S, restriction)
  return CongruencesOfPoset(PosetOfPrincipalCongruences(S, restriction));
end);

########################################################################
## MinimalCongruences
########################################################################

InstallMethod(MinimalCongruences, "for a congruence poset",
[IsCongruencePoset],
poset -> CongruencesOfPoset(poset){Positions(InDegrees(poset), 1)});

InstallMethod(MinimalCongruencesOfSemigroup, "for a semigroup", [IsSemigroup],
function(S)
  if HasLatticeOfCongruences(S) then
    return MinimalCongruences(LatticeOfCongruences(S));
  fi;
  return MinimalCongruences(PosetOfPrincipalCongruences(S));
end);

InstallMethod(MinimalLeftCongruencesOfSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if HasLatticeOfLeftCongruences(S) then
    return MinimalCongruences(LatticeOfLeftCongruences(S));
  fi;
  return MinimalCongruences(PosetOfPrincipalLeftCongruences(S));
end);

InstallMethod(MinimalRightCongruencesOfSemigroup, "for a semigroup",
[IsSemigroup],
function(S)
  if HasLatticeOfRightCongruences(S) then
    return MinimalCongruences(LatticeOfRightCongruences(S));
  fi;
  return MinimalCongruences(PosetOfPrincipalRightCongruences(S));
end);

InstallMethod(MinimalCongruencesOfSemigroup,
"for a semigroup and list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  return MinimalCongruences(PosetOfPrincipalCongruences(S, pairs));
end);

InstallMethod(MinimalRightCongruencesOfSemigroup,
"for a semigroup and list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  return MinimalCongruences(PosetOfPrincipalRightCongruences(S, pairs));
end);

InstallMethod(MinimalLeftCongruencesOfSemigroup,
"for a semigroup and list or collection",
[IsSemigroup, IsListOrCollection],
function(S, pairs)
  return MinimalCongruences(PosetOfPrincipalLeftCongruences(S, pairs));
end);

########################################################################
# Printing, viewing, dot strings etc
########################################################################

InstallMethod(ViewObj, "for a congruence poset", [IsCongruencePoset],
function(poset)
  if DigraphNrVertices(poset) = 0 then
    Print("<empty congruence poset>");
  else
    Print("<poset of ", DigraphNrVertices(poset), " congruences over ");
    ViewObj(UnderlyingSemigroupOfCongruencePoset(poset));
    Print(">");
  fi;
end);

InstallMethod(PrintObj, "for a congruence poset", [IsCongruencePoset],
function(poset)
  Print("PosetOfCongruences( ", CongruencesOfPoset(poset), " )");
end);

InstallMethod(DotString,
"for a congruence poset",
[IsCongruencePoset],
function(poset)
  # Call the below function, with default options
  return DotString(poset, rec());
end);

InstallMethod(DotString,
"for a congruence poset and a record",
[IsCongruencePoset, IsRecord],
function(poset, opts)
  local nrcongs, congs, S, symbols, i, nr, in_nbs, rel, str, j, k;
  nrcongs := DigraphNrVertices(poset);
  # Setup unbound options
  if not IsBound(opts.info) then
    opts.info := false;
  fi;
  if not IsBound(opts.numbers) then
    opts.numbers := (nrcongs < 40);
  fi;
  # If the user wants info, then change the node labels
  if opts.info = true then
    # The congruences are stored inside the poset object
    congs := CongruencesOfPoset(poset);
    S := Range(congs[1]);
    symbols := EmptyPlist(nrcongs);
    for i in [1 .. nrcongs] do
      nr := NrEquivalenceClasses(congs[i]);
      if nr = 1 then
        symbols[i] := "U";
      elif nr = Size(S) then
        symbols[i] := "T";
      elif IsReesCongruence(congs[i]) then
        symbols[i] := Concatenation("R", String(i));
      else
        symbols[i] := String(i);
      fi;
    od;
  else
    symbols := List([1 .. nrcongs], String);
  fi;

  in_nbs := InNeighbours(poset);
  rel := List([1 .. nrcongs], x -> Filtered(in_nbs[x], y -> x <> y));
  str := "";

  if opts.numbers then
    Append(str, "//dot\ngraph graphname {\n     node [shape=circle]\n");
  else
    Append(str, "//dot\ngraph graphname {\n     node [shape=point]\n");
  fi;

  for i in [1 .. Length(rel)] do
    j := Difference(rel[i], Union(rel{rel[i]}));
    i := symbols[i];
    for k in j do
      k := symbols[k];
      Append(str, Concatenation(i, " -- ", k, "\n"));
    od;
  od;

  Append(str, " }");

  return str;
end);
