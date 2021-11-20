###########################################################################
##
##  ideals-froidure-pin.gi
##  Copyright (C) 2014-21                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains method specific to ideals of semigroups.

if not IsBound(VerticesReachableFrom) then
  DeclareOperation("VerticesReachableFrom", [IsDigraph, IsPosInt]);
  InstallMethod(VerticesReachableFrom, "for a digraph and a vertex",
  [IsDigraph, IsPosInt],
  function(D, root)
    local N, index, current, succ, visited, prev, n, i, parent,
          have_visited_root;
    N := DigraphNrVertices(D);
    index := ListWithIdenticalEntries(N, 0);
    have_visited_root := false;
    index[root] := 1;
    current := root;
    succ := OutNeighbours(D);
    visited := [];
    parent := [];
    parent[root] := fail;
    repeat
      prev := current;
      for i in [index[current] .. Length(succ[current])] do
        n := succ[current][i];
        if n = root and have_visited_root = false then
           Add(visited, root);
           have_visited_root := true;
        elif index[n] = 0 then
          Add(visited, n);
            parent[n] := current;
            index[current] := i + 1;
            current := n;
            index[current] := 1;
            break;
        fi;
      od;
      if prev = current then
        current := parent[current];
      fi;
    until current = fail;
    return visited;
  end);
fi;

# We use the result of running the Froidure-Pin algorithm on the supersemigroup
# of an ideal to calculate elements, size, test membership, find idempotents,
# etc. We get a generating set and use that otherwise.

InstallMethod(PositionsInSupersemigroup,
"for a semigroup ideal with known generators",
[IsSemigroupIdeal and HasGeneratorsOfSemigroupIdeal and
 CanComputeFroidurePin],
function(I)
  local S, L, R, D, result, pos, x;
  S := SupersemigroupOfIdeal(I);
  L := LeftCayleyDigraph(S);
  R := RightCayleyDigraph(S);
  D := DigraphEdgeUnion(L, R);
  # This could be better, we could use the quotient of the above graph by its
  # sccs.

  result := [];
  for x in GeneratorsOfSemigroupIdeal(I) do
    pos := PositionCanonical(S, x);
    AddSet(result, pos);
    UniteSet(result, VerticesReachableFrom(D, pos));
  od;

  return result;
end);

InstallMethod(GeneratorsOfInverseSemigroup,
"for an inverse semigroup ideal with inverse op and generators",
[IsSemigroupIdeal and IsInverseSemigroup
 and IsGeneratorsOfInverseSemigroup and HasGeneratorsOfSemigroupIdeal],
GeneratorsOfSemigroup);

InstallMethod(Enumerator,
"semigroup ideal with generators and CanComputeFroidurePin",
[IsSemigroupIdeal and HasGeneratorsOfSemigroupIdeal and CanComputeFroidurePin],
2,  # To beat the method for IsSemigroup and CanComputeFroidurePin
function(I)
  local en, record;
  en := EnumeratorCanonical(SupersemigroupOfIdeal(I));

  record := rec();
  record.NumberElement := function(enum, elt)
    return Position(PositionsInSupersemigroup(I), Position(en, elt));
  end;

  record.ElementNumber := function(enum, nr)
    return en[PositionsInSupersemigroup(I)[nr]];
  end;

  record.IsBound\[\] := function(enum, nr)
    return IsBound(PositionsInSupersemigroup(I)[nr]);
  end;

  record.Length := enum -> Length(PositionsInSupersemigroup(I));

  return EnumeratorByFunctions(I, record);
end);

InstallMethod(Size, "for a semigroup ideal with generators",
[IsSemigroupIdeal and HasGeneratorsOfSemigroupIdeal],
function(I)
  return Length(Enumerator(I));
end);

InstallMethod(\in,
"for a multiplicative element and semigroup ideal with generators",
[IsMultiplicativeElement,
 IsSemigroup and CanComputeFroidurePin and IsSemigroupIdeal
 and HasGeneratorsOfSemigroupIdeal],
function(x, I)
  return Position(Enumerator(I), x) <> fail;
end);

# The method for GeneratorsOfSemigroup for a semigroup ideal must
# not rely in any way on the output of the Froidure-Pin algorithm when run on
# the ideal. In order to run the Froidure-Pin algorithm requires its input
# semigroup (ideal) to have a generating set, and so if the method below
# requires the output of the F-P algorithm (Green's relations, etc), then we
# get caught in an infinite loop: finding the generating set calls the F-P
# algorithm which tries to find a generating set, and so on.

InstallMethod(GeneratorsOfSemigroup, "for a semigroup ideal with generators",
[IsSemigroupIdeal and HasGeneratorsOfSemigroupIdeal],
function(I)
  local U;
  U := ClosureSemigroup(Semigroup(MinimalIdealGeneratingSet(I)),
                        Enumerator(I));
  return GeneratorsOfSemigroup(U);
end);

InstallMethod(Idempotents, "for a semigroup ideal with generators",
[IsSemigroupIdeal and HasGeneratorsOfSemigroupIdeal and CanComputeFroidurePin],
function(I)
  local S, en;
  S := SupersemigroupOfIdeal(I);
  en := EnumeratorCanonical(S);
  return en{IdempotentsSubset(S, PositionsInSupersemigroup(I))};
end);
