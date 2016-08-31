############################################################################
##
#W  pbr.gi
#Y  Copyright (C) 2015                                   Attila Egri-Nagy
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# This file contains an intitial implementation of partitioned binary
# relations (PBRs) as defined in:
#
# Paul Martin and Volodymyr Mazorchuk, Partitioned binary relations,
# Mathematica Scandinavica, v113, n1, p. 30-52, http://arxiv.org/abs/1102.0862

# Internally a PBR is stored as the adjacency list of digraph with
# vertices [1 .. 2 * n] for some n. More precisely if <x> is a PBR, then:
#
#   * <x![1]> is equal to <n>
#
#   * <x![i + 1]> is the vertices adjacent to <i>
#
# The number <n> is the *degree* of <x>.

#############################################################################
# Family and type.
#
# One per degree to avoid lists with pbrs of different degrees
# belonging to IsAssociativeElementCollection.
#############################################################################

BindGlobal("TYPES_PBR", []);
BindGlobal("TYPE_PBR",
function(n)

  if not IsInt(n) or n < 0 then
    ErrorNoReturn("Semigroups: TYPE_PBR: usage,\n",
                  "the argument must be a non-negative integer,");
  fi;

  n := n + 1; # since the degree can be 0

  if not IsBound(TYPES_PBR[n]) then
    TYPES_PBR[n] := NewType(NewFamily(Concatenation("PBRFamily", 
                                                    String(n - 1)),
                                      IsPBR,
                                      CanEasilySortElements,
                                      CanEasilySortElements),
                            IsPBR and IsPositionalObjectRep);
  fi;

  return TYPES_PBR[n];
end);

#############################################################################
# Pickler
#############################################################################

InstallMethod(IO_Pickle, "for a PBR",
[IsFile, IsPBR],
function(file, x)
  if IO_Write(file, "PABR") = fail then
    return IO_Error;
  fi;
  if IO_Pickle(file, List([1 .. 2 * x![1] + 1], i -> x![i])) = IO_Error then
    return IO_Error;
  fi;
  return IO_OK;
end);

IO_Unpicklers.PABR := function(file)
  local x;
  x := IO_Unpickle(file);
  if x = IO_Error then
    return IO_Error;
  fi;
  return Objectify(TYPE_PBR(x![1]), x);
end;

#############################################################################
# TODO the embeddings from the paper, AsPBR for a pbr (extend or restrict),
#############################################################################

InstallMethod(EmptyPBR, "for a pos int", [IsPosInt],
n -> PBRNC(List([1 .. n], y -> []), List([1 .. n], y -> [])));

InstallMethod(IdentityPBR, "for a pos int", [IsPosInt],
n -> PBRNC(List([1 .. n], y -> [-y]), List([1 .. n], y -> [y])));

InstallMethod(UniversalPBR, "for a pos in", [IsPosInt],
function(n)
  local x;
  x := Concatenation([-n .. -1], [1 .. n]);
  return PBRNC(List([1 .. n], y -> x), List([1 .. n], y -> x));
end);

# FIXME the following is temporary, with the current definition of
# IsGeneratorsOfInverseSemigroup for a pbr collection, the One of any element
# in the collection does not satisfy IsGeneratorsOfInverseSemigroup, and so it
# cannot be inverted.

InstallMethod(InverseMonoidByGenerators,
[IsPBRCollection],
function(coll)
  ErrorNoReturn("Semigroups: InverseMonoidByGenerators",
                "(for a pbr collection):\nnot yet implemented,");
end);

# FIXME see the comment above, this is not really correct.

InstallOtherMethod(InverseMutable, "for a PBR", [IsPBR],
function(x)
  #TODO change IsBlockBijection(AsBipartition(x)) to
  # IsBlockBijectionPBR.
  if IsPartialPermPBR(x) or
      (IsBipartitionPBR(x) and IsBlockBijection(AsBipartition(x))) then
    return Star(x);
  fi;
  return fail;
end);

# FIXME see the comment above, this is not really correct.

InstallMethod(IsGeneratorsOfInverseSemigroup, "for a pbr collection",
[IsPBRCollection],
function(coll)
  return ForAll(coll, IsBipartitionPBR)
         and IsGeneratorsOfInverseSemigroup(List(coll, AsBipartition));
end);

InstallMethod(StarOp, "for a pbr", [IsPBR],
function(x)
  local ext;
  ext := ShallowCopy(ExtRepOfObj(x) * -1);
  Apply(ext, ShallowCopy);
  Apply(ext[1], ShallowCopy);
  Apply(ext[2], ShallowCopy);
  return PBR(ext[2], ext[1]);
end);

InstallMethod(DegreeOfPBRCollection, "for a PBR collection",
[IsPBRCollection],
function(coll)
  local deg;

  if IsPBRSemigroup(coll) then
    return DegreeOfPBRSemigroup(coll);
  fi;

  deg := DegreeOfPBR(coll[1]);
  if not ForAll(coll, x -> DegreeOfPBR(x) = deg) then
    ErrorNoReturn("Semigroups: DegreeOfPBRCollection: usage,\n",
                  "the argument <coll> must be a collection of PBRs ",
                  "of equal degree,");
  fi;

  return deg;
end);

InstallMethod(IsGeneratorsOfSemigroup, "for a PBR collection",
[IsPBRCollection],
function(coll)
  local deg;
  deg := DegreeOfPBR(coll[1]);
  return ForAll(coll, x -> DegreeOfPBR(x) = deg);
end);

InstallMethod(IsBipartitionPBR, "for a pbr",
[IsPBR],
function(x)
  return IsEquivalenceBooleanMat(AsBooleanMat(x));
end);

InstallMethod(IsTransformationPBR, "for a pbr",
[IsPBR],
function(x)
  local n, i;

  n := x![1];
  for i in [2 .. n + 1] do
    if Length(x![i]) <> 1 or x![i][1] <= n
        or not i - 1 in x![x![i][1] + 1] then
      return false;
    fi;
  od;
  for i in [n + 2 .. 2 * n + 1] do
    if not ForAll(x![i], j -> j <= n and x![j + 1][1] = i - 1) then
      return false;
    fi;
  od;

  return true;
end);

InstallMethod(IsBlockBijectionPBR, "for a pbr",
[IsPBR],
function(x)
  return IsBipartitionPBR(x) and IsBlockBijection(AsBipartition(x));
end);

InstallMethod(IsPartialPermPBR, "for a pbr",
[IsPBR],
function(x)
  return IsBipartitionPBR(x) and IsPartialPermBipartition(AsBipartition(x));
end);

InstallMethod(IsPermPBR, "for a pbr",
[IsPBR],
function(x)
  return IsBipartitionPBR(x) and IsPermBipartition(AsBipartition(x));
end);

InstallMethod(IsDualTransformationPBR, "for a pbr",
[IsPBR],
function(x)
  return IsBipartitionPBR(x) and IsDualTransBipartition(AsBipartition(x));
end);

InstallMethod(NumberPBR, "for a pbr",
[IsPBR],
function(x)
  return NumberBooleanMat(AsBooleanMat(x));
end);

InstallMethod(PBRNumber, "for pos int and pos int",
[IsPosInt, IsPosInt],
function(nr, deg)
  return AsPBR(BooleanMatNumber(nr, 2 * deg));
end);

InstallMethod(IsEmptyPBR, "for a partition binary relation",
[IsPBR],
function(x)
  local n, i;

  n := x![1];
  for i in [2 .. 2 * n + 1] do
    if Length(x![i]) > 0 then
      return false;
    fi;
  od;
  return true;
end);

InstallMethod(IsIdentityPBR, "for a partition binary relation",
[IsPBR],
function(x)
  local n, i;

  n := x![1];
  for i in [2 .. n + 1] do
    if Length(x![i]) <> 1 or x![i][1] <> i + n - 1 then
      return false;
    fi;
  od;
  for i in [n + 2 .. 2 * n + 1] do
    if Length(x![i]) <> 1 or x![i][1] <> i - n - 1 then
      return false;
    fi;
  od;
  return true;
end);

InstallMethod(IsUniversalPBR, "for a partition binary relation",
[IsPBR],
function(x)
  local n, i;

  n := x![1];
  for i in [2 .. 2 * n + 1] do
    if Length(x![i]) < 2 * n then
      return false;
    fi;
  od;
  return true;
end);

InstallMethod(AsPBR, "for a partial perm and pos int",
[IsPartialPerm, IsPosInt],
function(x, deg)
  local left, right, j, i;

  left  := List([1 .. deg], x -> []);
  right := List([1 .. deg], x -> []);

  for i in [1 .. deg] do
    j := i ^ x;
    if j <= deg and j <> 0 then
      Add(left[i], -j);
      Add(right[j], i);
    fi;
  od;

  return PBR(left, right);
end);

InstallMethod(AsPBR, "for a partial perm",
[IsPartialPerm],
function(x)
  return AsPBR(x, Maximum(DegreeOfPartialPerm(x), CoDegreeOfPartialPerm(x)));
end);

InstallMethod(AsPBR, "for a transformation and pos int",
[IsTransformation, IsPosInt],
function(x, deg)
  local left, right, i;

  left  := List([1 .. deg], x -> []);
  right := List([1 .. deg], x -> []);

  for i in [1 .. deg] do
    Add(left[i], -(i ^ x));
    Add(right[i ^ x], i);
  od;

  return PBR(left, right);
end);

InstallMethod(AsPBR, "for a transformation",
[IsTransformation],
function(x)
  return AsPBR(x, DegreeOfTransformation(x));
end);

InstallMethod(AsPBR, "for a multiplicative element",
[IsMultiplicativeElement], x -> AsPBR(AsBipartition(x)));

InstallMethod(AsPBR,
"for an associative element and pos int",
[IsMultiplicativeElement, IsPosInt],
function(x, n)
  return AsPBR(AsBipartition(x, n));
end);

# TODO The following doesn't define a monoid embedding of P_n into PBR_n. What
# is a monoid embedding from P_n to PBR_n?

InstallMethod(AsPBR, "for a bipartition",
[IsBipartition], x -> AsPBR(x, DegreeOfBipartition(x)));

InstallMethod(AsPBR, "for a bipartition and pos int",
[IsBipartition, IsPosInt],
function(x, n)
  local deg, blocks, out, dom, block, i;

  deg    := DegreeOfBipartition(x);
  blocks := ExtRepOfObj(x);
  out    := [[], []];
  dom := Union([-n .. -1], [1 .. n]);

  for block in blocks do
    for i in block do
      if AbsInt(i) <= n then
        if i < 0 then
          out[2][-i] := Intersection(block, dom);
        else
          out[1][i] := Intersection(block, dom);
        fi;
      fi;
    od;
  od;
  for i in [deg + 1 .. n] do
    Add(out[1], []);
    Add(out[2], []);
  od;

  return PBRNC(out[1], out[2]);
end);

InstallMethod(AsPBR, "for a boolean matrix",
[IsBooleanMat],
function(x)
  local dim, succ;

  dim := DimensionOfMatrixOverSemiring(x);
  if not IsEvenInt(dim) then
    ErrorNoReturn("Semigroups: AsPBR: usage,\n",
                  "the boolean matrix <x> must be of even dimension,");
  fi;
  succ := Successors(x);
  return PBRNC(succ{[1 .. dim / 2]}, succ{[dim / 2 + 1 .. dim]});
end);

InstallMethod(AsPBR, "for a boolean mat and pos int",
[IsBooleanMat, IsPosInt],
function(mat, n)
  local m, nbs, k, i, j;

  if not IsEvenInt(n) then
    ErrorNoReturn("Semigroups: AsPBR: usage,\n",
                  "the second argument <n> must be even,");
  fi;

  m := DimensionOfMatrixOverSemiring(mat);

  if not IsEvenInt(m) then
    ErrorNoReturn("Semigroups: AsPBR: usage,\n",
                  "the boolean matrix <x> must be of even dimension,");
  fi;

  nbs := [List([1 .. n / 2], x -> []),
          List([1 .. n / 2], x -> [])];

  if n <= m then
    for i in [1 .. n / 2] do
      for j in [1 .. n] do
        if mat[i][j] then
          Add(nbs[1][i], j);
        fi;
      od;
    od;
    for i in [n / 2 + 1 .. n] do
      for j in [1 .. n] do
        if mat[i][j] then
          Add(nbs[2][i - n / 2], j);
        fi;
      od;
    od;
  else
    k := (n - m) / 2;

    for i in [1 .. m / 2] do
      for j in [1 .. m / 2] do
        if mat[i][j] then
          Add(nbs[1][i], j);
        fi;
      od;
      for j in [m / 2 + 1 .. m] do
        if mat[i][j] then
          Add(nbs[1][i], j + k);
        fi;
      od;
    od;
    for i in [m / 2 + 1 .. m] do
      for j in [1 .. m / 2] do
        if mat[i][j] then
          Add(nbs[2][i - m / 2], j);
        fi;
      od;
      for j in [m / 2 + 1 .. m] do
        if mat[i][j] then
          Add(nbs[2][i - m / 2], j + k);
        fi;
      od;
    od;
  fi;

  return PBRNC(nbs[1], nbs[2]);
end);

# TODO 2 arg version of this

InstallMethod(AsTransformation, "for a pbr",
[IsPBR],
function(x)
  local out, n, i;

  if not IsTransformationPBR(x) then
    ErrorNoReturn("Semigroups: AsTransformation: usage,\n",
                  "the argument <x> must be a transformation PBR,");
  fi;

  out := [];
  n := x![1];

  for i in [2 .. n + 1] do
    out[i - 1] := x![i][1] - n;
  od;

  return Transformation(out);
end);

# TODO 2 arg version of this

InstallMethod(AsPartialPerm, "for a pbr",
[IsPBR],
function(x)
  if not IsPartialPermPBR(x) then
    ErrorNoReturn("Semigroups: AsPartialPerm: usage,\n",
                  "the argument <x> must be a partial perm PBR,");
  fi;
  return AsPartialPerm(AsBipartition(x));
end);

# TODO 2 arg version of this

InstallMethod(AsPermutation, "for a pbr",
[IsPBR],
function(x)
  if not IsPermPBR(x) then
    ErrorNoReturn("Semigroups: AsPermutation: usage,\n",
                  "the argument <x> must be a permutation PBR,");
  fi;
  return AsPermutation(AsBipartition(x));
end);

InstallMethod(RandomPBR, "for a pos int", [IsPosInt],
function(n)
  local digraph;
  digraph := RandomDigraph(2 * n);
  return PBRNC(OutNeighbours(digraph){[1 .. n]},
               OutNeighbours(digraph){[n + 1 .. 2 * n]});
end);

InstallMethod(RandomPBR, "for a pos int", [IsPosInt, IsFloat],
function(n, p)
  local digraph;
  digraph := RandomDigraph(2 * n, p);
  return PBRNC(OutNeighbours(digraph){[1 .. n]},
               OutNeighbours(digraph){[n + 1 .. 2 * n]});
end);

InstallMethod(PBR, "for pair of dense list",
[IsDenseList, IsDenseList],
function(left, right)
  local deg, i;

  if Length(left) <> Length(right) then
    ErrorNoReturn("Semigroups: PBR: usage,\n",
                  "the arguments must have equal lengths,");
  fi;

  deg := Length(left);

  for i in [1 .. deg] do
    if not IsHomogeneousList(left[i]) or not IsHomogeneousList(right[i]) then
      ErrorNoReturn("Semigroups: PBR: usage,\n",
                    "the entries in the arguments must be homogeneous lists,");
    elif   not ForAll(left[i], j -> IsInt(j) and j <> 0
                                    and j <= deg and j >= -deg)
        or not ForAll(right[i], j -> IsInt(j) and j <> 0
                                     and j <= deg and j >= -deg) then
      ErrorNoReturn("Semigroups: PBR: usage,\n",
                    "the entries in the first argument must be integers ",
                    "in [", -deg, " .. -1]\n or [1 .. ", deg, "],");
    fi;
  od;
  return PBRNC(left, right);
end);

InstallGlobalFunction(PBRNC,
function(arg)
  local left, right, n, i, j;

  arg   := StructuralCopy(arg);
  left  := arg[1];  # things adjacent to positives
  right := arg[2];  # things adjacent to negatives

  n := Length(left);

  for i in [1 .. n] do
    for j in [1 .. Length(left[i])] do
      if left[i][j] < 0 then
        left[i][j] := -left[i][j] + n;
      fi;
    od;
    left[i] := ShallowCopy(left[i]);
    Sort(left[i]);
    for j in [1 .. Length(right[i])] do
      if right[i][j] < 0 then
        right[i][j] := -right[i][j] + n;
      fi;
    od;
    right[i] := ShallowCopy(right[i]);
    Sort(right[i]);
  od;
  MakeImmutable(arg);
  arg := Concatenation([Length(arg[1])], Concatenation(arg));
  return Objectify(TYPE_PBR(arg[1]), arg);
end);

InstallMethod(DegreeOfPBR, "for a pbr",
[IsPBR], pbr -> pbr![1]);

InstallMethod(\*, "for pbrs",
[IsPBR, IsPBR],
function(x, y)
  local n, out, x_seen, y_seen, empty, x_dfs, y_dfs, tmp, i, j;

  n := x![1];

  out := Concatenation([n], List([1 .. 2 * n], x -> BlistList([1 .. 2 * n],
                                                              [])));

  x_seen := BlistList([1 .. 2 * n], []);
  y_seen := BlistList([1 .. 2 * n], []);
  empty  := BlistList([1 .. 2 * n], []);

  x_dfs := function(i, adj) # starting in x
    local j;
    if x_seen[i] then
      return;
    fi;
    x_seen[i] := true;
    for j in x![i + 1] do
      if j <= n then
        adj[j] := true;
      else # j > n
        y_dfs(j - n, adj);
      fi;
    od;
    return;
  end;

  y_dfs := function(i, adj) # starting in y
    local j;
    if y_seen[i] then
      return;
    fi;
    y_seen[i] := true;
    for j in y![i + 1] do
      if j > n then
        adj[j] := true;
      else # j <= n
        x_dfs(j + n, adj);
      fi;
    od;
    return;
  end;

  tmp := [];

  for i in [1 .. n] do # find everything connected to vertex i
    for j in x![i + 1] do
      if j <= n then
        out[i + 1][j] := true;
      elif IsBound(tmp[j]) then
        UNITE_BLIST(out[i + 1], tmp[j]);
      else
        tmp[j] := BlistList([1 .. 2 * n], []);
        IntersectBlist(x_seen, empty);
        IntersectBlist(y_seen, empty);
        x_seen[i] := true;
        y_dfs(j - n, tmp[j]);
        UNITE_BLIST(out[i + 1], tmp[j]);
      fi;
      if SizeBlist(out[i + 1]) = 2 * n then
        break;
      fi;
    od;
  od;

  for i in [n + 1 .. 2 * n] do # find everything connected to vertex i
    for j in y![i + 1] do
      if j > n then
        out[i + 1][j] := true;
      elif IsBound(tmp[j]) then
        UNITE_BLIST(out[i + 1], tmp[j]);
      else
        tmp[j] := BlistList([1 .. 2 * n], []);
        IntersectBlist(x_seen, empty);
        IntersectBlist(y_seen, empty);
        y_seen[i] := true;
        x_dfs(j + n, tmp[j]);
        UNITE_BLIST(out[i + 1], tmp[j]);
      fi;
      if SizeBlist(out[i + 1]) = 2 * n then
        break;
      fi;
    od;
  od;
  for i in [2 .. 2 * n + 1] do
    out[i] := ListBlist([1 .. 2 * n], out[i]);
  od;
  return Objectify(TYPE_PBR(n), out);
end);

InstallMethod(ExtRepOfObj, "for a pbr",
[IsPBR],
function(x)
  local n, out, i, j, k;

  n := x![1];
  out := [[], []];
  for i in [0, 1] do
    for j in [1 + n * i .. n + n * i] do
      Add(out[i + 1], []);
      for k in x![j + 1] do
        if k > n then
          AddSet(out[i + 1][j - n * i], -(k - n));
        else
          AddSet(out[i + 1][j - n * i], k);
        fi;
      od;
    od;
  od;

  return out;
end);

# These ViewObj and PrintObj methods are here because Print(ext[1]) produces
# nicer output than Print(ViewString(ext[1])). The ViewString and PrintString
# methods are required for use in things like Green's relations.

InstallMethod(ViewObj, "for a pbr", [IsPBR], PrintObj);

InstallMethod(PrintObj, "for a pbr", [IsPBR],
function(x)
  local ext;

  ext := ExtRepOfObj(x);
  Print("\>\>PBR(\>\>", ext[1], "\<\<,");

  if Length(String(ext[1])) > 72 or Length(String(ext[2])) > 72 then
    Print("\n");
  else
    Print(" ");
  fi;

  Print("\>\>", ext[2], "\<\<\<\<)");
end);

InstallMethod(ViewString, "for a pbr", [IsPBR], PrintString);

InstallMethod(PrintString, "for a pbr",
[IsPBR],
function(x)
  local ext, str;

  ext := ExtRepOfObj(x);

  str := Concatenation("\>\>PBR(\>\>", ViewString(ext[1]), "\<\<,");

  if Length(String(ext[1])) > 72 or Length(String(ext[2])) > 72 then
    Append(str, "\n");
  else
    Append(str, " ");
  fi;

  Append(str, "\>\>");
  Append(str, ViewString(ext[2]));
  Append(str, "\<\<\<\<)");
  return str;
end);

InstallMethod(String, "for a pbr", [IsPBR],
function(x)
  local ext;
  ext := ExtRepOfObj(x);
  return Concatenation("PBR(", String(ext[1]), ", ", String(ext[2]), ")");
end);

InstallMethod(\=, "for pbrs",
[IsPBR, IsPBR],
function(x, y)
  local n, i;

  n := x![1];
  for i in [1 .. 2 * n + 1] do
    if x![i] <> y![i] then
      return false;
    fi;
  od;
  return true;
end);

InstallMethod(\<, "for pbrs",
[IsPBR, IsPBR],
function(x, y)
  local n, i;

  n := x![1];
  for i in [1 .. 2 * n + 1] do
    if x![i] < y![i] then
      return true;
    elif x![i] > y![i] then
      return false;
    fi;
  od;
  return false;
end);

InstallMethod(OneMutable, "for a pbr",
[IsPBR],
function(x)
  local n, out, i;

  n := x![1];
  out := [n];
  for i in [1 .. n] do
    out[i + 1] := [i + n];
    out[i + n + 1] := [i];
  od;
  return Objectify(TYPE_PBR(n), out);
end);
