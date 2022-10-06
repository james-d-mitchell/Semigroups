############################################################################
##
##  congruences/congwordgraph.gi
##  Copyright (C) 2022                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
############################################################################
##
## This file contains implementation for left, right, and two-sided
## congruences that are defined in terms of a IsWordGraph.

if not IsBoundGlobal("DigraphFollowPath") then
  BindGlobal("DigraphFollowPath", function(D, start, path)
    local out, current_node, current_edge;
    if start > DigraphNrVertices(D) then
      ErrorNoReturn(Concatenation("the 2nd argument (a pos. int.) must be in ",
                    StringFormatted("the range [{}, {}]",
                                    1,
                                    DigraphNrVertices(D))));
    fi;
    out := OutNeighbours(D);
    current_node := start;
    current_edge := 1;
    while current_edge <= Length(path)
        and IsBound(out[current_node][path[current_edge]]) do
      current_node := out[current_node][path[current_edge]];
      current_edge := current_edge + 1;
    od;
    if current_edge <= Length(path) then
      return fail;
    fi;
    return current_node;
  end);
fi;

InstallImmediateMethod(CanUseLibsemigroupsCongruence,
                       IsCongruenceByWordGraph,
                       0,
                       ReturnFalse);

InstallMethod(RightCongruenceByWordGraphNC,
"for CanUseFroidurePin and word graph",
[CanUseFroidurePin, IsWordGraph],
function(S, D)
  local fam, cong;
  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                               ElementsFamily(FamilyObj(S)));
  cong := Objectify(NewType(fam,
                            IsCongruenceByWordGraph and IsRightMagmaCongruence),
                    rec());
  SetIsRightSemigroupCongruence(cong, true);
  SetSource(cong, S);
  SetRange(cong, S);
  SetWordGraph(cong, D);
  return cong;
end);

InstallMethod(LeftCongruenceByWordGraphNC,
"for CanUseFroidurePin and word graph",
[CanUseFroidurePin, IsWordGraph],
function(S, D)
  local fam, cong;
  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                               ElementsFamily(FamilyObj(S)));
  cong := Objectify(NewType(fam,
                            IsCongruenceByWordGraph and IsLeftMagmaCongruence),
                    rec());
  SetIsLeftSemigroupCongruence(cong, true);
  SetSource(cong, S);
  SetRange(cong, S);
  SetWordGraph(cong, D);
  return cong;
end);

InstallMethod(ViewObj, "for a congruence by word graph",
[IsCongruenceByWordGraph],
function(C)
  Print(ViewString(C));
end);

InstallMethod(ViewString, "for a right congruence by word graph",
[IsCongruenceByWordGraph and IsRightSemigroupCongruence],
function(C)
  return StringFormatted(
    "<right congruence by word graph over {}>",
    ViewString(Source(C)));
end);

InstallMethod(ViewString, "for a left congruence by word graph",
[IsCongruenceByWordGraph and IsLeftSemigroupCongruence],
function(C)
  return StringFormatted(
    "<left congruence by word graph over {}>",
    ViewString(Source(C)));
end);

# Mandatory methods for CanComputeEquivalenceRelationPartition

InstallMethod(EquivalenceRelationPartitionWithSingletons,
"for a right congruence by word graph",
[IsCongruenceByWordGraph and IsRightSemigroupCongruence],
function(C)
  local D, S, words, result, index, i;
  D := WordGraph(C);
  S := EnumeratorCanonical(Source(C));
  words := List(S, x -> MinimalFactorization(Source(C), x));
  result := List([1 .. DigraphNrVertices(D)], x -> []);
  for i in [1 .. Length(words)] do
    index := DigraphFollowPath(D, 1, words[i]);
    Add(result[index], S[i]);
  od;
  return result;
end);

InstallMethod(EquivalenceRelationPartitionWithSingletons,
"for a left congruence by word graph",
[IsCongruenceByWordGraph and IsLeftSemigroupCongruence],
function(C)
  local D, S, words, result, index, i;
  D := WordGraph(C);
  S := EnumeratorCanonical(Source(C));
  words := List(S, x -> Reversed(MinimalFactorization(Source(C), x)));
  result := List([1 .. DigraphNrVertices(D)], x -> []);
  for i in [1 .. Length(words)] do
    index := DigraphFollowPath(D, 1, words[i]);
    Add(result[index], S[i]);
  od;
  return result;
end);

InstallMethod(CongruenceTestMembershipNC,
"for a right congruence by word graph, mult. elt. and mult. elt.",
[IsCongruenceByWordGraph and IsRightSemigroupCongruence,
 IsMultiplicativeElement,
 IsMultiplicativeElement],
function(C, lhop, rhop)
  local D;
  D := WordGraph(C);
  lhop := MinimalFactorization(Source(C), lhop);
  rhop := MinimalFactorization(Source(C), rhop);
  return DigraphFollowPath(D, 1, lhop) = DigraphFollowPath(D, 1, rhop);
end);

InstallMethod(CongruenceTestMembershipNC,
"for a left congruence by word graph, mult. elt. and mult. elt.",
[IsCongruenceByWordGraph and IsLeftSemigroupCongruence,
 IsMultiplicativeElement,
 IsMultiplicativeElement],
function(C, lhop, rhop)
  local D;
  D := WordGraph(C);
  lhop := Reversed(MinimalFactorization(Source(C), lhop));
  rhop := Reversed(MinimalFactorization(Source(C), rhop));
  return DigraphFollowPath(D, 1, lhop) = DigraphFollowPath(D, 1, rhop);
end);

InstallMethod(ImagesElm,
"for a right congruence by word graph and mult. elt.",
[IsCongruenceByWordGraph and IsRightSemigroupCongruence,
 IsMultiplicativeElement],
function(C, x)
  local part, D;
  part := EquivalenceRelationPartitionWithSingletons(C);
  D := WordGraph(C);
  x := MinimalFactorization(Source(C), x);
  return part[DigraphFollowPath(D, 1, x)];
end);

InstallMethod(ImagesElm,
"for a left congruence by word graph and mult. elt.",
[IsCongruenceByWordGraph and IsLeftSemigroupCongruence,
 IsMultiplicativeElement],
function(C, x)
  local part, D;
  part := EquivalenceRelationPartitionWithSingletons(C);
  D := WordGraph(C);
  x := Reversed(MinimalFactorization(Source(C), x));
  return part[DigraphFollowPath(D, 1, x)];
end);

# Non-mandatory methods where we can do better than the default methods

InstallMethod(NrEquivalenceClasses, "for a congruence by word graph",
[IsCongruenceByWordGraph],
C -> DigraphNrVertices(WordGraph(C)));
