############################################################################
##
##  congruences/congrms.gi
##  Copyright (C) 2015                                   Michael C. Torpey
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
## This file contains methods for congruences on finite (0-)simple Rees
## (0-)matrix semigroups, using linked triples.  See Howie 3.5-6, and see
## MT's reports "Computing with Congruences on Finite 0-Simple Semigroups"
## and MSc thesis "Computing with Semigroup Congruences" chapter 3.
##

InstallGlobalFunction(RMSCongruenceByLinkedTriple,
function(S, n, colBlocks, rowBlocks)
  local mat, g;
  mat := Matrix(S);
  g := UnderlyingSemigroup(S);

  # Basic checks
  if not IsNormal(g, n) then
    ErrorNoReturn("the 2nd argument (a group) is not a normal ",
                  "subgroup of the underlying semigroup of the 1st ",
                  "argument (a Rees matrix semigroup)");
  elif not IsList(colBlocks) or not ForAll(colBlocks, IsList) then
    ErrorNoReturn("the 3rd argument must be a list of lists");
  elif not IsList(rowBlocks) or not ForAll(rowBlocks, IsList) then
    ErrorNoReturn("the 4th argument must be a list of lists");
  elif SortedList(Flat(colBlocks)) <> [1 .. Size(mat[1])] then
    ErrorNoReturn("the 3rd argument (a list of lists) does not partition ",
                  "the columns of the matrix of the 1st argument (a Rees",
                  " matrix semigroup)");
  elif SortedList(Flat(rowBlocks)) <> [1 .. Size(mat)] then
    ErrorNoReturn("the 4th argument (a list of lists) does not partition ",
                  "the columns of the matrix of the 1st argument (a Rees",
                  " matrix semigroup)");
  fi;

  if IsLinkedTriple(S, n, colBlocks, rowBlocks) then
    return RMSCongruenceByLinkedTripleNC(S, n, colBlocks, rowBlocks);
  else
    ErrorNoReturn("invalid triple");
  fi;
end);

InstallGlobalFunction(RZMSCongruenceByLinkedTriple,
function(S, n, colBlocks, rowBlocks)
  local mat, g;
  mat := Matrix(S);
  g := UnderlyingSemigroup(S);

  # Basic checks
  if not (IsGroup(g) and IsGroup(n)) then
    ErrorNoReturn("the underlying semigroup of the 1st argument ",
                  "(a Rees 0-matrix semigroup) is not a group");
  elif not IsNormal(g, n) then
    ErrorNoReturn("the 2nd argument (a group) is not a normal ",
                  "subgroup of the underlying semigroup of the 1st ",
                  "argument (a Rees 0-matrix semigroup)");
  elif not IsList(colBlocks) or not ForAll(colBlocks, IsList) then
    ErrorNoReturn("the 3rd argument is not a list of lists");
  elif not IsList(rowBlocks) or not ForAll(rowBlocks, IsList) then
    ErrorNoReturn("the 4th argument is not a list of lists");
  elif SortedList(Flat(colBlocks)) <> [1 .. Size(mat[1])] then
    ErrorNoReturn("the 3rd argument (a list of lists) does not partition ",
                  "the columns of the matrix of the 1st argument (a Rees",
                  " 0-matrix semigroup)");
  elif SortedList(Flat(rowBlocks)) <> [1 .. Size(mat)] then
    ErrorNoReturn("the 4th argument (a list of lists) does not partition ",
                  "the columns of the matrix of the 1st argument (a Rees",
                  " 0-matrix semigroup)");
  fi;

  if IsLinkedTriple(S, n, colBlocks, rowBlocks) then
    return RZMSCongruenceByLinkedTripleNC(S, n, colBlocks, rowBlocks);
  else
    ErrorNoReturn("invalid triple");
  fi;
end);

InstallGlobalFunction(RMSCongruenceByLinkedTripleNC,
function(S, n, colBlocks, rowBlocks)
  local fam, cong, colLookup, rowLookup, i, j;
  # Sort the blocks
  colBlocks := SSortedList(colBlocks);
  rowBlocks := SSortedList(rowBlocks);
  # Calculate lookup table for equivalence relations
  colLookup := [];
  rowLookup := [];
  for i in [1 .. Length(colBlocks)] do
    for j in colBlocks[i] do
      colLookup[j] := i;
    od;
  od;
  for i in [1 .. Length(rowBlocks)] do
    for j in rowBlocks[i] do
      rowLookup[j] := i;
    od;
  od;
  # Construct the object
  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                               ElementsFamily(FamilyObj(S)));
  cong := Objectify(NewType(fam, IsRMSCongruenceByLinkedTriple),
                    rec(n := n,
                        colBlocks := colBlocks,
                        colLookup := colLookup,
                        rowBlocks := rowBlocks,
                        rowLookup := rowLookup));
  SetSource(cong, S);
  SetRange(cong, S);
  return cong;
end);

InstallGlobalFunction(RZMSCongruenceByLinkedTripleNC,
function(S, n, colBlocks, rowBlocks)
  local fam, cong, colLookup, rowLookup, i, j;
  # Sort the blocks
  colBlocks := SSortedList(colBlocks);
  rowBlocks := SSortedList(rowBlocks);
  # Calculate lookup table for equivalence relations
  colLookup := [];
  rowLookup := [];
  for i in [1 .. Length(colBlocks)] do
    for j in colBlocks[i] do
      colLookup[j] := i;
    od;
  od;
  for i in [1 .. Length(rowBlocks)] do
    for j in rowBlocks[i] do
      rowLookup[j] := i;
    od;
  od;
  # Construct the object
  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                               ElementsFamily(FamilyObj(S)));
  cong := Objectify(NewType(fam, IsRZMSCongruenceByLinkedTriple),
                    rec(n := n,
                        colBlocks := colBlocks,
                        colLookup := colLookup,
                        rowBlocks := rowBlocks,
                        rowLookup := rowLookup));
  SetSource(cong, S);
  SetRange(cong, S);
  return cong;
end);

InstallMethod(ViewObj,
"for Rees matrix semigroup congruence by linked triple",
[IsRMSCongruenceByLinkedTriple],
function(cong)
  Print("<semigroup congruence over ");
  ViewObj(Range(cong));
  Print(" with linked triple (",
        StructureDescription(cong!.n:short), ",",
        Size(cong!.colBlocks), ",",
        Size(cong!.rowBlocks), ")>");
end);

InstallMethod(ViewObj,
"for Rees zero-matrix semigroup congruence by linked triple",
[IsRZMSCongruenceByLinkedTriple],
function(cong)
  Print("<semigroup congruence over ");
  ViewObj(Range(cong));
  Print(" with linked triple (",
        StructureDescription(cong!.n:short), ",",
        Size(cong!.colBlocks), ",",
        Size(cong!.rowBlocks), ")>");
end);

InstallMethod(CongruencesOfSemigroup,
"for finite simple Rees matrix semigroup",
[IsReesMatrixSemigroup and IsSimpleSemigroup and IsFinite],
function(S)
  local subpartitions, congs, mat, g, colBlocksList,
        rowBlocksList, n, colBlocks, rowBlocks;

  # Function to compute all subsets of a relation given by partitions
  subpartitions := function(part)
    local l;
    # Replace each class with a list of all partitions of that class
    l := List(part, PartitionsSet);
    # Produce all the combinations of partitions of classes
    l := Cartesian(l);
    # Concatenate these lists to produce complete partitions of the set
    l := List(l, Concatenation);
    # Finally sort each of these into the canonical order of its new classes
    l := List(l, SSortedList);
    return l;
  end;

  congs := [];
  mat := Matrix(S);
  g := UnderlyingSemigroup(S);

  # No need to add the universal congruence

  # Compute all column and row relations which are subsets of the max relations
  colBlocksList := subpartitions([[1 .. Size(mat[1])]]);
  rowBlocksList := subpartitions([[1 .. Size(mat)]]);

  # Go through all triples and check
  for n in NormalSubgroups(g) do
    for colBlocks in colBlocksList do
      for rowBlocks in rowBlocksList do
        if IsLinkedTriple(S, n, colBlocks, rowBlocks) then
          Add(congs,
              RMSCongruenceByLinkedTripleNC(S, n, colBlocks, rowBlocks));
        fi;
      od;
    od;
  od;

  return congs;
end);

InstallMethod(CongruencesOfSemigroup,
"for finite 0-simple Rees 0-matrix semigroup",
[IsReesZeroMatrixSemigroup and IsZeroSimpleSemigroup and IsFinite],
function(S)
  local congs, mat, g, AddRelation, maxColBlocks, maxRowBlocks,
        i, j, u, v, n, colBlocks, rowBlocks, colBlocksList, rowBlocksList,
        subpartitions;

  # Function to compute all subsets of a relation given by partitions
  subpartitions := function(part)
    local l;
    # Replace each class with a list of all partitions of that class
    l := List(part, PartitionsSet);
    # Produce all the combinations of partitions of classes
    l := Cartesian(l);
    # Concatenate these lists to produce complete partitions of the set
    l := List(l, Concatenation);
    # Finally sort each of these into the canonical order of its new classes
    l := List(l, SSortedList);
    return l;
  end;

  congs := [];
  mat := Matrix(S);
  g := UnderlyingSemigroup(S);

  # This function combines two congruence classes
  AddRelation := function(R, x, y)
    local xClass, yClass;
    xClass := PositionProperty(R, class -> x in class);
    yClass := PositionProperty(R, class -> y in class);
    if xClass <> yClass then
      Append(R[xClass], R[yClass]);
      Remove(R, yClass);
    fi;
  end;

  # Construct maximum column relation
  maxColBlocks := List([1 .. Size(mat[1])], i -> [i]);
  for i in [1 .. Size(mat[1])] do
    for j in [i + 1 .. Size(mat[1])] do
      if ForAll([1 .. Size(mat)],
                u -> ((mat[u][i] = 0) = (mat[u][j] = 0))) then
        AddRelation(maxColBlocks, i, j);
      fi;
    od;
  od;

  # Construct maximum row relation
  maxRowBlocks := List([1 .. Size(mat)], u -> [u]);
  for u in [1 .. Size(mat)] do
    for v in [u + 1 .. Size(mat)] do
      if ForAll([1 .. Size(mat[1])],
                i -> ((mat[u][i] = 0) = (mat[v][i] = 0))) then
        AddRelation(maxRowBlocks, u, v);
      fi;
    od;
  od;

  # Add the universal congruence
  Add(congs, UniversalSemigroupCongruence(S));

  # Compute all column and row relations which are subsets of the max relations
  colBlocksList := subpartitions(maxColBlocks);
  rowBlocksList := subpartitions(maxRowBlocks);

  # Go through all triples and check
  for n in NormalSubgroups(g) do
    for colBlocks in colBlocksList do
      for rowBlocks in rowBlocksList do
        if IsLinkedTriple(S, n, colBlocks, rowBlocks) then
          Add(congs,
              RZMSCongruenceByLinkedTripleNC(S, n, colBlocks, rowBlocks));
        fi;
      od;
    od;
  od;

  return congs;
end);

InstallMethod(IsLinkedTriple,
"for Rees matrix semigroup, group, and two lists",
[IsReesMatrixSemigroup,
 IsGroup, IsDenseList, IsDenseList],
function(S, n, colBlocks, rowBlocks)
  local mat, block, bi, bj, i, j, u, v, bu, bv;
  # Check the semigroup is valid
  if not IsFinite(S) then
    ErrorNoReturn("the 1st argument (a Rees matrix semigroup) is not finite");
  elif not IsSimpleSemigroup(S) then
    ErrorNoReturn("the 1st argument (a Rees matrix semigroup) is not simple");
  fi;
  mat := Matrix(S);
  # Check axiom (L2) from Howie p.86, then call NC function
  # Go through the column blocks
  for block in colBlocks do
    # Check q-condition for all pairs of columns in this block (L2)
    for bi in [1 .. Size(block)] do
      for bj in [bi + 1 .. Size(block)] do
        i := block[bi];
        j := block[bj];
        # Check all pairs of rows (u,v)
        for u in [1 .. Size(mat)] do
          for v in [u + 1 .. Size(mat)] do
            if not (mat[u][i] * mat[v][i] ^ -1 * mat[v][j] * mat[u][j] ^ -1)
                in n then
              return false;
            fi;
          od;
        od;
      od;
    od;
  od;

  # Go through the row blocks
  for block in rowBlocks do
    # Check q-condition for all pairs of rows in this block (L2)
    for bu in [1 .. Size(block)] do
      for bv in [bu + 1 .. Size(block)] do
        u := block[bu];
        v := block[bv];
        # Check all pairs of columns (i,j)
        for i in [1 .. Size(mat[1])] do
          for j in [i + 1 .. Size(mat[1])] do
            if not (mat[u][i] * mat[v][i] ^ -1 * mat[v][j] * mat[u][j] ^ -1)
                in n then
              return false;
            fi;
          od;
        od;
      od;
    od;
  od;
  return true;
end);

InstallMethod(IsLinkedTriple,
"for Rees 0-matrix semigroup, group, and two lists",
[IsReesZeroMatrixSemigroup,
 IsGroup, IsDenseList, IsDenseList],
function(S, n, colBlocks, rowBlocks)
  local mat, block, i, j, u, v, bi, bj, bu, bv;
  # Check the semigroup is valid
  if not IsFinite(S) then
    ErrorNoReturn("the 1st argument (a Rees 0-matrix semigroup) is not finite");
  elif not IsZeroSimpleSemigroup(S) then
    ErrorNoReturn("the 1st argument (a Rees 0-matrix semigroup) is ",
                  "not 0-simple");
  fi;
  mat := Matrix(S);
  # Check axioms (L1) and (L2) from Howie p.86, then call NC function
  # Go through the column blocks
  for block in colBlocks do
    for bj in [2 .. Size(block)] do
      # Check columns have zeroes in all the same rows (L1)
      for u in [1 .. Size(mat)] do
        if (mat[u][block[1]] = 0) <> (mat[u][block[bj]] = 0) then
          return false;
        fi;
      od;
    od;
    # Check q-condition for all pairs of columns in this block (L2)
    for bi in [1 .. Size(block)] do
      for bj in [bi + 1 .. Size(block)] do
        i := block[bi];
        j := block[bj];
        # Check all pairs of rows (u,v)
        for u in [1 .. Size(mat)] do
          if mat[u][i] = 0 then
            continue;
          fi;
          for v in [u + 1 .. Size(mat)] do
            if mat[v][i] = 0 then
              continue;
            fi;
            if not (mat[u][i] * mat[v][i] ^ -1 * mat[v][j] * mat[u][j] ^ -1)
                in n then
              return false;
            fi;
          od;
        od;
      od;
    od;
  od;

  # Go through the row blocks
  for block in rowBlocks do
    for bv in [2 .. Size(block)] do
      # Check rows have zeroes in all the same columns (L1)
      for i in [1 .. Size(mat[1])] do
        if (mat[block[1]][i] = 0) <> (mat[block[bv]][i] = 0) then
          return false;
        fi;
      od;
    od;
    # Check q-condition for all pairs of rows in this block (L2)
    for bu in [1 .. Size(block)] do
      for bv in [bu + 1 .. Size(block)] do
        u := block[bu];
        v := block[bv];
        # Check all pairs of columns (i,j)
        for i in [1 .. Size(mat[1])] do
          if mat[u][i] = 0 then
            continue;
          fi;
          for j in [i + 1 .. Size(mat[1])] do
            if mat[u][j] = 0 then
              continue;
            fi;
            if not (mat[u][i] * mat[v][i] ^ -1 * mat[v][j] * mat[u][j] ^ -1)
                in n then
              return false;
            fi;
          od;
        od;
      od;
    od;
  od;
  return true;
end);

BindGlobal("LinkedElement",
function(elm)
  local mat, i, u, v, j;
  mat := Matrix(ReesMatrixSemigroupOfFamily(FamilyObj(elm)));
  i := elm[1];  # Column no
  u := elm[3];  # Row no
  if IsReesMatrixSemigroupElement(elm) then
    # RMS case
    return mat[1][i] * elm[2] * mat[u][1];
  else
    # RZMS case
    for v in [1 .. Size(mat)] do
      if mat[v][i] <> 0 then
        break;
      fi;
    od;
    for j in [1 .. Size(mat[1])] do
      if mat[u][j] <> 0 then
        break;
      fi;
    od;
    return mat[v][i] * elm[2] * mat[u][j];
  fi;
end);

InstallMethod(\=,
"for two Rees matrix semigroup congruences by linked triple",
[IsRMSCongruenceByLinkedTriple, IsRMSCongruenceByLinkedTriple],
function(c1, c2)
  return(Range(c1) = Range(c2) and
         c1!.n = c2!.n and
         c1!.colBlocks = c2!.colBlocks and
         c1!.rowBlocks = c2!.rowBlocks);
end);

InstallMethod(\=,
"for two Rees 0-matrix semigroup congruences by linked triple",
[IsRZMSCongruenceByLinkedTriple, IsRZMSCongruenceByLinkedTriple],
function(c1, c2)
  return(Range(c1) = Range(c2) and
         c1!.n = c2!.n and
         c1!.colBlocks = c2!.colBlocks and
         c1!.rowBlocks = c2!.rowBlocks);
end);

InstallMethod(IsSubrelation,
"for two Rees matrix semigroup congruences by linked triple",
[IsRMSCongruenceByLinkedTriple, IsRMSCongruenceByLinkedTriple],
function(cong1, cong2)
  # Tests whether cong2 is a subcongruence of cong1
  if Range(cong1) <> Range(cong2) then
    ErrorNoReturn("the ranges of the arguments (congruences) do not coincide");
  fi;
  return IsSubgroup(cong1!.n, cong2!.n)
         and ForAll(cong2!.colBlocks,
                    b2 -> ForAny(cong1!.colBlocks, b1 -> IsSubset(b1, b2)))
         and ForAll(cong2!.rowBlocks,
                    b2 -> ForAny(cong1!.rowBlocks, b1 -> IsSubset(b1, b2)));
end);

InstallMethod(IsSubrelation,
"for two Rees 0-matrix semigroup congruences by linked triple",
[IsRZMSCongruenceByLinkedTriple, IsRZMSCongruenceByLinkedTriple],
function(cong1, cong2)
  # Tests whether cong2 is a subcongruence of cong1
  if Range(cong1) <> Range(cong2) then
    ErrorNoReturn("the ranges of the arguments (congruences) do not coincide");
  fi;
  return IsSubgroup(cong1!.n, cong2!.n)
         and ForAll(cong2!.colBlocks,
                    b2 -> ForAny(cong1!.colBlocks, b1 -> IsSubset(b1, b2)))
         and ForAll(cong2!.rowBlocks,
                    b2 -> ForAny(cong1!.rowBlocks, b1 -> IsSubset(b1, b2)));
end);

InstallMethod(CongruenceTestMembershipNC,
"for RMS congruence by linked triple and two RMS elements",
[IsRMSCongruenceByLinkedTriple,
 IsReesMatrixSemigroupElement, IsReesMatrixSemigroupElement],
function(cong, elm1, elm2)
  local i, a, u, j, b, v, mat, gpElm;
  # Read the elements as (i,a,u) and (j,b,v)
  i := elm1[1];
  a := elm1[2];
  u := elm1[3];
  j := elm2[1];
  b := elm2[2];
  v := elm2[3];

  # First, the columns and rows must be related
  if not (cong!.colLookup[i] = cong!.colLookup[j] and
          cong!.rowLookup[u] = cong!.rowLookup[v]) then
    return false;
  fi;

  # Finally, check Lemma 3.5.6(2) in Howie, with row 1 and column 1
  mat := Matrix(Range(cong));
  gpElm := mat[1][i] * a * mat[u][1] * Inverse(mat[1][j] * b * mat[v][1]);
  return gpElm in cong!.n;
end);

InstallMethod(CongruenceTestMembershipNC,
"for RZMS congruence by linked triple and two RZMS elements",
[IsRZMSCongruenceByLinkedTriple,
 IsReesZeroMatrixSemigroupElement, IsReesZeroMatrixSemigroupElement],
function(cong, elm1, elm2)
  local S, i, a, u, j, b, v, mat, rows, cols, col, row, gpElm;
  S := Range(cong);

  # Handling the case when one or more of the pair are zero
  if elm1 = elm2 then
    return true;
  elif elm1 = MultiplicativeZero(S) or elm2 = MultiplicativeZero(S) then
    return false;
  fi;

  # Read the elements as (i,a,u) and (j,b,v)
  i := elm1[1];
  a := elm1[2];
  u := elm1[3];
  j := elm2[1];
  b := elm2[2];
  v := elm2[3];

  # First, the columns and rows must be related
  if not (cong!.colLookup[i] = cong!.colLookup[j] and
          cong!.rowLookup[u] = cong!.rowLookup[v]) then
    return false;
  fi;

  # Finally, check Lemma 3.5.6(2) in Howie
  mat := Matrix(S);
  rows := mat;
  cols := TransposedMat(mat);
  # Pick a valid column and row
  col := PositionProperty(rows[u], x -> x <> 0);
  row := PositionProperty(cols[i], x -> x <> 0);
  gpElm := mat[row][i] * a * mat[u][col] *
           Inverse(mat[row][j] * b * mat[v][col]);
  return gpElm in cong!.n;
end);

InstallMethod(ImagesElm,
"for Rees matrix semigroup congruence by linked triple and element",
[IsRMSCongruenceByLinkedTriple, IsReesMatrixSemigroupElement],
function(cong, elm)
  local S, mat, images, i, a, u, j, v, nElm, b;
  S := Range(cong);
  mat := Matrix(S);
  if not elm in S then
    ErrorNoReturn("the 2nd argument (an element of a Rees matrix ",
                  "semigroup) does not belong to the range of the ",
                  "1st argument (a congruence)");
  fi;
  # List of all elements congruent to elm under cong
  images := [];
  # Read the element as (i,a,u)
  i := elm[1];
  a := elm[2];
  u := elm[3];
  # Construct congruent elements as (j,b,v)
  for j in cong!.colBlocks[cong!.colLookup[i]] do
    for v in cong!.rowBlocks[cong!.rowLookup[u]] do
      for nElm in cong!.n do
        # Might be better to use congruence classes after all
        b := mat[1][j] ^ -1 * nElm * mat[1][i] * a * mat[u][1]
             * mat[v][1] ^ -1;
        Add(images, RMSElement(S, j, b, v));
      od;
    od;
  od;
  return images;
end);

InstallMethod(ImagesElm,
"for Rees 0-matrix semigroup congruence by linked triple and element",
[IsRZMSCongruenceByLinkedTriple, IsReesZeroMatrixSemigroupElement],
function(cong, elm)
  local S, mat, images, i, a, u, row, col, j, b, v, nElm;
  S := Range(cong);
  mat := Matrix(S);
  if not elm in S then
    ErrorNoReturn("the 2nd argument (an element of a Rees 0-matrix ",
                  "semigroup) does not belong to the range of the ",
                  "1st argument (a congruence)");
  fi;
  # Special case for 0
  if elm = MultiplicativeZero(S) then
    return [elm];
  fi;
  # List of all elements congruent to elm under cong
  images := [];
  # Read the element as (i,a,u)
  i := elm[1];
  a := elm[2];
  u := elm[3];
  # Find a non-zero row for this class of columns
  for row in [1 .. Size(mat)] do
    if mat[row][i] <> 0 then
      break;
    fi;
  od;
  # Find a non-zero column for this class of rows
  for col in [1 .. Size(mat[1])] do
    if mat[u][col] <> 0 then
      break;
    fi;
  od;

  # Construct congruent elements as (j,b,v)
  for j in cong!.colBlocks[cong!.colLookup[i]] do
    for v in cong!.rowBlocks[cong!.rowLookup[u]] do
      for nElm in cong!.n do
        # Might be better to use congruence classes after all
        b := mat[row][j] ^ -1
             * nElm
             * mat[row][i]
             * a
             * mat[u][col]
             * mat[v][col] ^ -1;
        Add(images, RMSElement(S, j, b, v));
      od;
    od;
  od;
  return images;
end);

InstallMethod(EquivalenceClasses,
"for Rees matrix semigroup congruence by linked triple",
[IsRMSCongruenceByLinkedTriple],
function(cong)
  local list, S, g, n, colBlocks, rowBlocks, colClass, rowClass, rep, elm;
  list := [];
  S := Range(cong);
  g := UnderlyingSemigroup(S);
  n := cong!.n;
  colBlocks := cong!.colBlocks;
  rowBlocks := cong!.rowBlocks;
  for colClass in [1 .. Size(colBlocks)] do
    for rowClass in [1 .. Size(rowBlocks)] do
      for rep in List(RightCosets(g, n), Representative) do
        elm := RMSElement(S,
                          colBlocks[colClass][1],
                          rep,
                          rowBlocks[rowClass][1]);
        Add(list, EquivalenceClassOfElement(cong, elm));
      od;
    od;
  od;
  return list;
end);

InstallMethod(EquivalenceClasses,
"for Rees 0-matrix semigroup congruence by linked triple",
[IsRZMSCongruenceByLinkedTriple],
function(cong)
  local list, S, g, n, colBlocks, rowBlocks, colClass, rowClass, rep, elm;
  list := [];
  S := Range(cong);
  g := UnderlyingSemigroup(S);
  n := cong!.n;
  colBlocks := cong!.colBlocks;
  rowBlocks := cong!.rowBlocks;
  for colClass in [1 .. Size(colBlocks)] do
    for rowClass in [1 .. Size(rowBlocks)] do
      for rep in List(RightCosets(g, n), Representative) do
        elm := RMSElement(S,
                          colBlocks[colClass][1],
                          rep,
                          rowBlocks[rowClass][1]);
        Add(list, EquivalenceClassOfElement(cong, elm));
      od;
    od;
  od;
  # Add the zero class
  Add(list, EquivalenceClassOfElement(cong, MultiplicativeZero(S)));
  return list;
end);

InstallMethod(NrEquivalenceClasses,
"for Rees matrix semigroup congruence by linked triple",
[IsRMSCongruenceByLinkedTriple],
function(cong)
  local S, g;
  S := Range(cong);
  g := UnderlyingSemigroup(S);
  return(Index(g, cong!.n)             # Number of cosets of n
         * Size(cong!.colBlocks)       # Number of column blocks
         * Size(cong!.rowBlocks));     # Number of row blocks
end);

InstallMethod(NrEquivalenceClasses,
"for Rees 0-matrix semigroup congruence by linked triple",
[IsRZMSCongruenceByLinkedTriple],
function(cong)
  local S, g;
  S := Range(cong);
  g := UnderlyingSemigroup(S);
  return(Index(g, cong!.n)             # Number of cosets of n
         * Size(cong!.colBlocks)       # Number of column blocks
         * Size(cong!.rowBlocks)       # Number of row blocks
         + 1);                         # Class containing zero
end);

InstallMethod(Enumerator,
"for RMS congruence class by linked triple",
[IsRMSCongruenceClassByLinkedTriple],
function(class)
  return ImagesElm(EquivalenceClassRelation(class), Representative(class));
end);

InstallMethod(Enumerator,
"for RZMS congruence class by linked triple",
[IsRZMSCongruenceClassByLinkedTriple],
function(class)
  return ImagesElm(EquivalenceClassRelation(class), Representative(class));
end);

InstallMethod(JoinSemigroupCongruences,
"for two Rees matrix semigroup congruences by linked triple",
[IsRMSCongruenceByLinkedTriple, IsRMSCongruenceByLinkedTriple],
function(c1, c2)
  local gens, n, colBlocks, rowBlocks, block, b1, j, pos;
  if Range(c1) <> Range(c2) then
    ErrorNoReturn("the ranges of the arguments (congruences) do not coincide");
  fi;
  # n is the product of the normal subgroups
  gens := Concatenation(GeneratorsOfGroup(c1!.n), GeneratorsOfGroup(c2!.n));
  n := Subgroup(UnderlyingSemigroup(Range(c1)), gens);
  # Calculate the join of the column and row relations
  colBlocks := StructuralCopy(c1!.colBlocks);
  rowBlocks := StructuralCopy(c1!.rowBlocks);
  for block in c2!.colBlocks do
    b1 := PositionProperty(colBlocks, cb -> block[1] in cb);
    for j in [2 .. Size(block)] do
      if not block[j] in colBlocks[b1] then
        # Combine the classes
        pos := PositionProperty(colBlocks, cb -> block[j] in cb);
        Append(colBlocks[b1], colBlocks[pos]);
        Unbind(colBlocks[pos]);
      fi;
    od;
    colBlocks := Compacted(colBlocks);
  od;
  for block in c2!.rowBlocks do
    b1 := PositionProperty(rowBlocks, rb -> block[1] in rb);
    for j in [2 .. Size(block)] do
      if not block[j] in rowBlocks[b1] then
        # Combine the classes
        pos := PositionProperty(rowBlocks, rb -> block[j] in rb);
        Append(rowBlocks[b1], rowBlocks[pos]);
        Unbind(rowBlocks[pos]);
      fi;
    od;
    rowBlocks := Compacted(rowBlocks);
  od;
  colBlocks := SortedList(List(colBlocks, block -> SortedList(block)));
  rowBlocks := SortedList(List(rowBlocks, block -> SortedList(block)));
  # Make the congruence and return it
  return RMSCongruenceByLinkedTripleNC(Range(c1), n, colBlocks, rowBlocks);
end);

InstallMethod(JoinSemigroupCongruences,
"for two Rees 0-matrix semigroup congruences by linked triple",
[IsRZMSCongruenceByLinkedTriple, IsRZMSCongruenceByLinkedTriple],
function(c1, c2)
  local gens, n, colBlocks, rowBlocks, block, b1, j, pos;
  if Range(c1) <> Range(c2) then
    ErrorNoReturn("the ranges of the arguments (congruences) do not coincide");
  fi;
  # n is the product of the normal subgroups
  gens := Concatenation(GeneratorsOfGroup(c1!.n), GeneratorsOfGroup(c2!.n));
  n := Subgroup(UnderlyingSemigroup(Range(c1)), gens);
  # Calculate the join of the column and row relations
  colBlocks := StructuralCopy(c1!.colBlocks);
  rowBlocks := StructuralCopy(c1!.rowBlocks);
  for block in c2!.colBlocks do
    b1 := PositionProperty(colBlocks, cb -> block[1] in cb);
    for j in [2 .. Size(block)] do
      if not block[j] in colBlocks[b1] then
        # Combine the classes
        pos := PositionProperty(colBlocks, cb -> block[j] in cb);
        Append(colBlocks[b1], colBlocks[pos]);
        Unbind(colBlocks[pos]);
      fi;
    od;
    colBlocks := Compacted(colBlocks);
  od;
  for block in c2!.rowBlocks do
    b1 := PositionProperty(rowBlocks, rb -> block[1] in rb);
    for j in [2 .. Size(block)] do
      if not block[j] in rowBlocks[b1] then
        # Combine the classes
        pos := PositionProperty(rowBlocks, rb -> block[j] in rb);
        Append(rowBlocks[b1], rowBlocks[pos]);
        Unbind(rowBlocks[pos]);
      fi;
    od;
    rowBlocks := Compacted(rowBlocks);
  od;
  colBlocks := SortedList(List(colBlocks, block -> SortedList(block)));
  rowBlocks := SortedList(List(rowBlocks, block -> SortedList(block)));
  # Make the congruence and return it
  return RZMSCongruenceByLinkedTriple(Range(c1), n, colBlocks, rowBlocks);
end);

InstallMethod(MeetSemigroupCongruences,
"for two Rees matrix semigroup congruences by linked triple",
[IsRMSCongruenceByLinkedTriple, IsRMSCongruenceByLinkedTriple],
function(c1, c2)
  local n, colBlocks, cols, rowBlocks, rows, i, block, j, u, v;
  if Range(c1) <> Range(c2) then
    ErrorNoReturn("the ranges of the arguments (congruences) do not coincide");
  fi;
  # n is the intersection of the two normal subgroups
  n := Intersection(c1!.n, c2!.n);
  # Calculate the intersection of the column and row relations
  colBlocks := [];
  cols := [1 .. Size(c1!.colLookup)];
  rowBlocks := [];
  rows := [1 .. Size(c1!.rowLookup)];
  for i in [1 .. Size(cols)] do
    if cols[i] = 0 then
      continue;
    fi;
    block := Intersection(c1!.colBlocks[c1!.colLookup[i]],
                          c2!.colBlocks[c2!.colLookup[i]]);
    for j in block do
      cols[j] := 0;
    od;
    Add(colBlocks, block);
  od;
  for u in [1 .. Size(rows)] do
    if rows[u] = 0 then
      continue;
    fi;
    block := Intersection(c1!.rowBlocks[c1!.rowLookup[u]],
                          c2!.rowBlocks[c2!.rowLookup[u]]);
    for v in block do
      rows[v] := 0;
    od;
    Add(rowBlocks, block);
  od;
  # Make the congruence and return it
  return RMSCongruenceByLinkedTripleNC(Range(c1), n, colBlocks, rowBlocks);
end);

InstallMethod(MeetSemigroupCongruences,
"for two Rees 0-matrix semigroup congruences by linked triple",
[IsRZMSCongruenceByLinkedTriple, IsRZMSCongruenceByLinkedTriple],
function(c1, c2)
  local n, colBlocks, cols, rowBlocks, rows, i, block, j, u, v;
  if Range(c1) <> Range(c2) then
    ErrorNoReturn("the ranges of the arguments (congruences) do not coincide");
  fi;
  # n is the intersection of the two normal subgroups
  n := Intersection(c1!.n, c2!.n);
  # Calculate the intersection of the column and row relations
  colBlocks := [];
  cols := [1 .. Size(c1!.colLookup)];
  rowBlocks := [];
  rows := [1 .. Size(c1!.rowLookup)];
  for i in [1 .. Size(cols)] do
    if cols[i] = 0 then
      continue;
    fi;
    block := Intersection(c1!.colBlocks[c1!.colLookup[i]],
                          c2!.colBlocks[c2!.colLookup[i]]);
    for j in block do
      cols[j] := 0;
    od;
    Add(colBlocks, block);
  od;
  for u in [1 .. Size(rows)] do
    if rows[u] = 0 then
      continue;
    fi;
    block := Intersection(c1!.rowBlocks[c1!.rowLookup[u]],
                          c2!.rowBlocks[c2!.rowLookup[u]]);
    for v in block do
      rows[v] := 0;
    od;
    Add(rowBlocks, block);
  od;
  # Make the congruence and return it
  return RZMSCongruenceByLinkedTripleNC(Range(c1), n, colBlocks, rowBlocks);
end);

InstallMethod(RMSCongruenceClassByLinkedTriple,
"for semigroup congruence by linked triple, a coset and two positive integers",
[IsRMSCongruenceByLinkedTriple, IsRightCoset, IsPosInt, IsPosInt],
function(cong, nCoset, colClass, rowClass)
  local g;
  g := UnderlyingSemigroup(Range(cong));
  if not (ActingDomain(nCoset) = cong!.n and IsSubset(g, nCoset)) then
    ErrorNoReturn("the 2nd argument (a right coset) is not a coset of the",
                  " normal subgroup of defining the 1st argument (a ",
                  "congruence)");
  elif not colClass in [1 .. Size(cong!.colBlocks)] then
    ErrorNoReturn("the 3rd argument (a pos. int.) is out of range");
  elif not rowClass in [1 .. Size(cong!.rowBlocks)] then
    ErrorNoReturn("the 4th argument (a pos. int.) is out of range");
  fi;
  return RMSCongruenceClassByLinkedTripleNC(cong, nCoset, colClass, rowClass);
end);

InstallMethod(RZMSCongruenceClassByLinkedTriple,
"for semigroup congruence by linked triple, a coset and two positive integers",
[IsRZMSCongruenceByLinkedTriple,
 IsRightCoset, IsPosInt, IsPosInt],
function(cong, nCoset, colClass, rowClass)
  local g;
  g := UnderlyingSemigroup(Range(cong));
  if not (ActingDomain(nCoset) = cong!.n and IsSubset(g, nCoset)) then
    ErrorNoReturn("the 2nd argument (a right coset) is not a coset of the",
                  " normal subgroup of defining the 1st argument (a ",
                  "congruence)");
  elif not colClass in [1 .. Size(cong!.colBlocks)] then
    ErrorNoReturn("the 3rd argument (a pos. int.) is out of range");
  elif not rowClass in [1 .. Size(cong!.rowBlocks)] then
    ErrorNoReturn("the 4th argument (a pos. int.) is out of range");
  fi;
  return RZMSCongruenceClassByLinkedTripleNC(cong, nCoset, colClass, rowClass);
end);

InstallMethod(RMSCongruenceClassByLinkedTripleNC,
"for semigroup congruence by linked triple, a coset and two positive integers",
[IsRMSCongruenceByLinkedTriple,
 IsRightCoset, IsPosInt, IsPosInt],
function(cong, nCoset, colClass, rowClass)
  local fam, class;
  fam := FamilyObj(Range(cong));
  class := Objectify(NewType(fam, IsRMSCongruenceClassByLinkedTriple),
                     rec(nCoset := nCoset,
                         colClass := colClass,
                         rowClass := rowClass));
  SetParentAttr(class, Range(cong));
  SetEquivalenceClassRelation(class, cong);
  SetRepresentative(class, CanonicalRepresentative(class));
  return class;
end);

InstallMethod(RZMSCongruenceClassByLinkedTripleNC,
"for semigroup congruence by linked triple, a coset and two positive integers",
[IsRZMSCongruenceByLinkedTriple,
 IsRightCoset, IsPosInt, IsPosInt],
function(cong, nCoset, colClass, rowClass)
  local fam, class;
  fam := FamilyObj(Range(cong));
  class := Objectify(NewType(fam, IsRZMSCongruenceClassByLinkedTriple),
                     rec(nCoset := nCoset,
                         colClass := colClass,
                         rowClass := rowClass));
  SetParentAttr(class, Range(cong));
  SetEquivalenceClassRelation(class, cong);
  SetRepresentative(class, CanonicalRepresentative(class));
  return class;
end);

InstallMethod(EquivalenceClassOfElement,
"for Rees matrix semigroup congruence by linked triple and element",
[IsRMSCongruenceByLinkedTriple, IsReesMatrixSemigroupElement],
function(cong, elm)
  # Check that the args make sense
  if not elm in Range(cong) then
    ErrorNoReturn("the 2nd argument (an element of a Rees matrix ",
                  "semigroup) does not belong to the range of the 1st ",
                  "argument (a congruence)");
  fi;
  return EquivalenceClassOfElementNC(cong, elm);
end);

InstallMethod(EquivalenceClassOfElement,
"for Rees 0-matrix semigroup congruence by linked triple and an element",
[IsRZMSCongruenceByLinkedTriple, IsReesZeroMatrixSemigroupElement],
function(cong, elm)
  # Check that the args make sense
  if not elm in Range(cong) then
    ErrorNoReturn("the 2nd argument (an element of a Rees matrix ",
                  "semigroup) does not belong to the range of the 1st ",
                  "argument (a congruence)");
  fi;
  return EquivalenceClassOfElementNC(cong, elm);
end);

InstallMethod(EquivalenceClassOfElementNC,
"for Rees matrix semigroup congruence by linked triple and element",
[IsRMSCongruenceByLinkedTriple, IsReesMatrixSemigroupElement],
function(cong, elm)
  local fam, nCoset, colClass, rowClass, class;
  fam := CollectionsFamily(FamilyObj(elm));
  nCoset := RightCoset(cong!.n, LinkedElement(elm));
  colClass := cong!.colLookup[elm[1]];
  rowClass := cong!.rowLookup[elm[3]];
  class := Objectify(NewType(fam, IsRMSCongruenceClassByLinkedTriple),
                     rec(nCoset := nCoset,
                         colClass := colClass,
                         rowClass := rowClass));
  SetParentAttr(class, Range(cong));
  SetEquivalenceClassRelation(class, cong);
  SetRepresentative(class, elm);
  return class;
end);

InstallMethod(EquivalenceClassOfElementNC,
"for Rees 0-matrix semigroup congruence by linked triple and element",
[IsRZMSCongruenceByLinkedTriple, IsReesZeroMatrixSemigroupElement],
function(cong, elm)
  local fam, class, nCoset, colClass, rowClass;
  fam := CollectionsFamily(FamilyObj(elm));
  if elm = MultiplicativeZero(Range(cong)) then
    class := Objectify(NewType(fam, IsRZMSCongruenceClassByLinkedTriple),
                       rec(nCoset := 0));
  else
    nCoset := RightCoset(cong!.n, LinkedElement(elm));
    colClass := cong!.colLookup[elm[1]];
    rowClass := cong!.rowLookup[elm[3]];
    class := Objectify(NewType(fam, IsRZMSCongruenceClassByLinkedTriple),
                       rec(nCoset := nCoset,
                           colClass := colClass,
                           rowClass := rowClass));
  fi;
  SetParentAttr(class, Range(cong));
  SetEquivalenceClassRelation(class, cong);
  SetRepresentative(class, elm);
  return class;
end);

InstallMethod(\in,
"for Rees matrix semigroup element and a congruence class by linked triple",
[IsReesMatrixSemigroupElement, IsRMSCongruenceClassByLinkedTriple],
function(elm, class)
  local S, cong;
  cong := EquivalenceClassRelation(class);
  S := Range(cong);
  return(elm in S and
         cong!.colLookup[elm[1]] = class!.colClass and
         cong!.rowLookup[elm[3]] = class!.rowClass and
         LinkedElement(elm) in class!.nCoset);
end);

InstallMethod(\in,
"for Rees 0-matrix semigroup element and a congruence class by linked triple",
[IsReesZeroMatrixSemigroupElement, IsRZMSCongruenceClassByLinkedTriple],
function(elm, class)
  local S, cong;
  cong := EquivalenceClassRelation(class);
  S := Range(cong);
  # Special case for 0 and {0}
  if class!.nCoset = 0 then
    return elm = MultiplicativeZero(S);
  fi;
  # Otherwise
  return(elm in S and
         cong!.colLookup[elm[1]] = class!.colClass and
         cong!.rowLookup[elm[3]] = class!.rowClass and
         LinkedElement(elm) in class!.nCoset);
end);

InstallMethod(\*,
"for two RMS congruence classes by linked triple",
[IsRMSCongruenceClassByLinkedTriple, IsRMSCongruenceClassByLinkedTriple],
function(c1, c2)
  local elm;
  if not EquivalenceClassRelation(c1) = EquivalenceClassRelation(c2) then
    ErrorNoReturn("the arguments (congruence classes) do not ",
                  "belong to the same congruence");
  fi;
  elm := Representative(c1) * Representative(c2);
  return EquivalenceClassOfElementNC(EquivalenceClassRelation(c1), elm);
end);

InstallMethod(\*,
"for two RZMS congruence classes by linked triple",
[IsRZMSCongruenceClassByLinkedTriple, IsRZMSCongruenceClassByLinkedTriple],
function(c1, c2)
  local elm;
  if not EquivalenceClassRelation(c1) = EquivalenceClassRelation(c2) then
    ErrorNoReturn("the arguments (congruence classes) do not ",
                  "belong to the same congruence");
  fi;
  elm := Representative(c1) * Representative(c2);
  return EquivalenceClassOfElementNC(EquivalenceClassRelation(c1), elm);
end);

InstallMethod(Size,
"for RMS congruence class by linked triple",
[IsRMSCongruenceClassByLinkedTriple],
function(class)
  local cong;
  cong := EquivalenceClassRelation(class);
  return(Size(cong!.n) *
         Size(cong!.colBlocks[class!.colClass]) *
         Size(cong!.rowBlocks[class!.rowClass]));
end);

InstallMethod(Size,
"for RZMS congruence class by linked triple",
[IsRZMSCongruenceClassByLinkedTriple],
function(class)
  local cong;
  # Special case for {0}
  if class!.nCoset = 0 then
    return 1;
  fi;
  # Otherwise
  cong := EquivalenceClassRelation(class);
  return(Size(cong!.n) *
         Size(cong!.colBlocks[class!.colClass]) *
         Size(cong!.rowBlocks[class!.rowClass]));
end);

InstallMethod(\=,
"for two congruence classes by linked triple",
[IsRMSCongruenceClassByLinkedTriple, IsRMSCongruenceClassByLinkedTriple],
function(c1, c2)
  return(c1!.nCoset = c2!.nCoset and
         c1!.colClass = c2!.colClass and
         c1!.rowClass = c2!.rowClass);
end);

InstallMethod(\=,
"for two congruence classes by linked triple",
[IsRZMSCongruenceClassByLinkedTriple, IsRZMSCongruenceClassByLinkedTriple],
function(c1, c2)
  # Special case for {0}
  if c1!.nCoset = 0 and c2!.nCoset = 0 then
    return true;
  fi;
  # Otherwise
  return(c1!.nCoset = c2!.nCoset and
         c1!.colClass = c2!.colClass and
         c1!.rowClass = c2!.rowClass);
end);

InstallMethod(CanonicalRepresentative,
"for Rees matrix semigroup congruence class by linked triple",
[IsRMSCongruenceClassByLinkedTriple],
function(class)
  local cong, S, i, u, mat, a;
  cong := EquivalenceClassRelation(class);
  S := Range(cong);
  # Pick the first row and column from the classes
  i := cong!.colBlocks[class!.colClass][1];
  u := cong!.rowBlocks[class!.rowClass][1];
  # Pick another row and column
  mat := Matrix(S);
  a := mat[1][i] ^ -1
       * CanonicalRightCosetElement(cong!.n, Representative(class!.nCoset))
       * mat[u][1] ^ -1;
  return RMSElement(S, i, a, u);
end);

InstallMethod(CanonicalRepresentative,
"for Rees 0-matrix semigroup congruence class by linked triple",
[IsRZMSCongruenceClassByLinkedTriple],
function(class)
  local cong, S, mat, i, u, v, j, a;
  cong := EquivalenceClassRelation(class);
  S := Range(cong);
  # Special case for {0}
  if class!.nCoset = 0 then
    return MultiplicativeZero(S);
  fi;
  # Pick the first row and column from the classes
  i := cong!.colBlocks[class!.colClass][1];
  u := cong!.rowBlocks[class!.rowClass][1];
  # Pick another row and column with appropriate non-zero entries
  mat := Matrix(S);
  for v in [1 .. Size(mat)] do
    if mat[v][i] <> 0 then
      break;
    fi;
  od;
  for j in [1 .. Size(mat[1])] do
    if mat[u][j] <> 0 then
      break;
    fi;
  od;
  a := mat[v][i] ^ -1
       * CanonicalRightCosetElement(cong!.n, Representative(class!.nCoset))
       * mat[u][j] ^ -1;
  return RMSElement(S, i, a, u);
end);

InstallMethod(GeneratingPairsOfMagmaCongruence,
"for Rees matrix semigroup congruence by linked triple",
[IsRMSCongruenceByLinkedTriple],
function(cong)
  local S, G, m, pairs, n_gens, col_pairs, bl, j, row_pairs, max, n, cp, rp,
        pair_no, r, c;
  S := Range(cong);
  G := UnderlyingSemigroup(S);
  m := Matrix(S);
  pairs := [];

  # Normal subgroup elements to identify with id
  n_gens := GeneratorsOfSemigroup(cong!.n);

  # Pairs that generate the columns relation
  col_pairs := [];
  for bl in cong!.colBlocks do
    for j in [2 .. Size(bl)] do
      Add(col_pairs, [bl[1], bl[j]]);
    od;
  od;

  # Pairs that generate the rows relation
  row_pairs := [];
  for bl in cong!.rowBlocks do
    for j in [2 .. Size(bl)] do
      Add(row_pairs, [bl[1], bl[j]]);
    od;
  od;

  # Collate into RMS element pairs
  max := Maximum(Length(n_gens), Length(col_pairs), Length(row_pairs));
  pairs := EmptyPlist(max);
  # Set default values in case a list has length 0
  n := One(G);
  cp := [1, 1];
  rp := [1, 1];
  # Iterate through all 3 lists together
  for pair_no in [1 .. max] do
    # If any list has run out, just keep using the last entry or default value
    if pair_no <= Length(n_gens) then
      n := n_gens[pair_no];
    fi;
    if pair_no <= Length(col_pairs) then
      cp := col_pairs[pair_no];
    fi;
    if pair_no <= Length(row_pairs) then
      rp := row_pairs[pair_no];
    fi;
    # Choose r and c s.t. m[r][cp[1]] and m[rp[1]][c] are both non-zero
    # (since there are no zeroes, we can just use 1 for both)
    r := 1;
    c := 1;
    # Make the pair and add it
    pairs[pair_no] :=
      [RMSElement(S, cp[1], m[r][cp[1]] ^ -1 * n * m[rp[1]][c] ^ -1, rp[1]),
       RMSElement(S, cp[2], m[r][cp[2]] ^ -1 * m[rp[2]][c] ^ -1, rp[2])];
  od;
  return pairs;
end);

InstallMethod(GeneratingPairsOfMagmaCongruence,
"for Rees 0-matrix semigroup congruence by linked triple",
[IsRZMSCongruenceByLinkedTriple],
function(cong)
  local S, G, m, pairs, n_gens, col_pairs, bl, j, row_pairs, max, n, cp, rp,
        pair_no, r, c;
  S := Range(cong);
  G := UnderlyingSemigroup(S);
  m := Matrix(S);
  pairs := [];

  # Normal subgroup elements to identify with id
  n_gens := GeneratorsOfSemigroup(cong!.n);

  # Pairs that generate the columns relation
  col_pairs := [];
  for bl in cong!.colBlocks do
    for j in [2 .. Size(bl)] do
      Add(col_pairs, [bl[1], bl[j]]);
    od;
  od;

  # Pairs that generate the rows relation
  row_pairs := [];
  for bl in cong!.rowBlocks do
    for j in [2 .. Size(bl)] do
      Add(row_pairs, [bl[1], bl[j]]);
    od;
  od;

  # Collate into RMS element pairs
  max := Maximum(Length(n_gens), Length(col_pairs), Length(row_pairs));
  pairs := EmptyPlist(max);
  # Set default values in case a list has length 0
  n := One(G);
  cp := [1, 1];
  rp := [1, 1];
  # Iterate through all 3 lists together
  for pair_no in [1 .. max] do
    # If any list has run out, just keep using the last entry or default value
    if pair_no <= Length(n_gens) then
      n := n_gens[pair_no];
    fi;
    if pair_no <= Length(col_pairs) then
      cp := col_pairs[pair_no];
    fi;
    if pair_no <= Length(row_pairs) then
      rp := row_pairs[pair_no];
    fi;
    # Choose r and c s.t. m[r][cp[1]] and m[rp[1]][c] are both non-zero
    r := First([1 .. Length(m)], r -> m[r][cp[1]] <> 0);
    c := First([1 .. Length(m[1])], c -> m[rp[1]][c] <> 0);
    # Make the pair and add it
    pairs[pair_no] :=
      [RMSElement(S, cp[1], m[r][cp[1]] ^ -1 * n * m[rp[1]][c] ^ -1, rp[1]),
       RMSElement(S, cp[2], m[r][cp[2]] ^ -1 * m[rp[2]][c] ^ -1, rp[2])];
  od;
  return pairs;
end);

InstallMethod(AsSemigroupCongruenceByGeneratingPairs,
"for semigroup congruence",
[IsSemigroupCongruence],
function(cong)
  local S, pairs;
  S := Range(cong);
  pairs := GeneratingPairsOfMagmaCongruence(cong);
  return SemigroupCongruenceByGeneratingPairs(S, pairs);
end);

InstallMethod(AsRMSCongruenceByLinkedTriple,
"for semigroup congruence by generating pairs",
[IsSemigroupCongruence and HasGeneratingPairsOfMagmaCongruence],
function(cong)
  local pairs, S, g, mat, colLookup, rowLookup, n, find, union, pair, u, v, i,
        j, normalise, colBlocks, rowBlocks;
  # Extract some information
  pairs := GeneratingPairsOfSemigroupCongruence(cong);
  S := Range(cong);
  g := UnderlyingSemigroup(S);
  mat := Matrix(S);

  # Lookup tables for the column and row equivalences
  colLookup := [1 .. Size(mat[1])];
  rowLookup := [1 .. Size(mat)];

  # Normal subgroup
  n := Subgroup(g, []);

  # Functions for union-find
  find := function(table, n)
    while table[n] <> n do
      n := table[n];
    od;
    return n;
  end;

  union := function(table, x, y)
    x := find(table, x);
    y := find(table, y);
    if x < y then
      table[y] := x;
    elif y < x then
      table[x] := y;
    fi;
  end;

  for pair in pairs do
    # If this pair adds no information, ignore it
    if pair[1] = pair[2] then
      continue;
    fi;

    # TODO(later) use UF from datastructures
    # Associate the columns and rows
    union(colLookup, pair[1][1], pair[2][1]);
    union(rowLookup, pair[1][3], pair[2][3]);

    # Associate group entries in the normal subgroup
    n := ClosureGroup(n, LinkedElement(pair[1]) * LinkedElement(pair[2]) ^ -1);

    # Ensure linkedness
    for v in [2 .. Size(mat)] do
      n := ClosureGroup(n, mat[1][pair[1][1]]
                           * mat[v][pair[1][1]] ^ -1
                           * mat[v][pair[2][1]]
                           * mat[1][pair[2][1]] ^ -1);
    od;
    for j in [2 .. Size(mat[1])] do
      n := ClosureGroup(n, mat[pair[1][3]][1]
                           * mat[pair[2][3]][1] ^ -1
                           * mat[pair[2][3]][j]
                           * mat[pair[1][3]][j] ^ -1);
    od;
  od;

  # Normalise lookup tables
  normalise := function(table)
    local ht, next, newtab, i, ii;
    ht := HTCreate(1);
    next := 1;
    newtab := [];
    for i in [1 .. Size(table)] do
      ii := find(table, i);
      newtab[i] := HTValue(ht, ii);
      if newtab[i] = fail then
        newtab[i] := next;
        HTAdd(ht, ii, next);
        next := next + 1;
      fi;
    od;
    return newtab;
  end;
  colLookup := normalise(colLookup);
  rowLookup := normalise(rowLookup);

  # Make blocks
  colBlocks := List([1 .. Maximum(colLookup)], x -> []);
  rowBlocks := List([1 .. Maximum(rowLookup)], x -> []);
  for i in [1 .. Size(colLookup)] do
    Add(colBlocks[colLookup[i]], i);
  od;
  for u in [1 .. Size(rowLookup)] do
    Add(rowBlocks[rowLookup[u]], u);
  od;

  # Make n normal
  n := NormalClosure(g, n);

  cong := RMSCongruenceByLinkedTriple(S, n, colBlocks, rowBlocks);
  SetGeneratingPairsOfMagmaCongruence(cong, pairs);
  return cong;
end);

InstallMethod(AsRZMSCongruenceByLinkedTriple,
"for semigroup congruence by generating pairs",
[IsSemigroupCongruence and HasGeneratingPairsOfMagmaCongruence],
function(cong)
  local pairs, S, g, mat, colLookup, rowLookup, n, find, union, pair, u, v, i,
        j, normalise, colBlocks, rowBlocks;

  # Extract some information
  pairs := GeneratingPairsOfSemigroupCongruence(cong);
  S := Range(cong);
  if not IsReesZeroMatrixSemigroup(S) then
    ErrorNoReturn("the range of the argument (a congruence) is not a Rees ",
                  "0-matrix semigroup");
  fi;
  g := UnderlyingSemigroup(S);
  mat := Matrix(S);

  # Lookup tables for the column and row equivalences
  colLookup := [1 .. Size(mat[1])];
  rowLookup := [1 .. Size(mat)];

  # Normal subgroup
  n := Subgroup(g, []);

  # Functions for union-find
  find := function(table, n)
    while table[n] <> n do
      n := table[n];
    od;
    return n;
  end;

  union := function(table, x, y)
    x := find(table, x);
    y := find(table, y);
    if x < y then
      table[y] := x;
    elif y < x then
      table[x] := y;
    fi;
  end;

  for pair in pairs do
    # If this pair adds no information, ignore it
    if pair[1] = pair[2] then
      continue;
    fi;

    # Does this relate any non-zero elements to zero?
    if pair[1] = MultiplicativeZero(S)
        or pair[2] = MultiplicativeZero(S)
        or ForAny([1 .. Size(mat)],
                  u -> (mat[u][pair[1][1]] = 0)
                  <>   (mat[u][pair[2][1]] = 0))
        or ForAny([1 .. Size(mat[1])],
                  i -> (mat[pair[1][3]][i] = 0)
                  <>   (mat[pair[2][3]][i] = 0)) then
      return UniversalSemigroupCongruence(S);
    fi;

    # TODO(now) use UF from datastructures
    # Associate the columns and rows
    union(colLookup, pair[1][1], pair[2][1]);
    union(rowLookup, pair[1][3], pair[2][3]);

    # Associate group entries in the normal subgroup
    n := ClosureGroup(n, LinkedElement(pair[1]) * LinkedElement(pair[2]) ^ -1);

    # Ensure linkedness
    u := PositionProperty([1 .. Size(mat)], u -> mat[u][pair[1][1]] <> 0);
    for v in [u + 1 .. Size(mat)] do
      if mat[v][pair[1][1]] = 0 then
        continue;
      fi;
      n := ClosureGroup(n, mat[u][pair[1][1]]
                           * mat[v][pair[1][1]] ^ -1
                           * mat[v][pair[2][1]]
                           * mat[u][pair[2][1]] ^ -1);
    od;
    i := PositionProperty([1 .. Size(mat[1])], k -> mat[pair[1][3]][k] <> 0);
    for j in [i + 1 .. Size(mat[1])] do
      if mat[pair[1][3]][j] = 0 then
        continue;
      fi;
      n := ClosureGroup(n, mat[pair[1][3]][i]
                           * mat[pair[2][3]][i] ^ -1
                           * mat[pair[2][3]][j]
                           * mat[pair[1][3]][j] ^ -1);
    od;
  od;

  # Normalise lookup tables
  normalise := function(table)
    local ht, next, newtab, i, ii;
    ht := HTCreate(1);
    next := 1;
    newtab := [];
    for i in [1 .. Size(table)] do
      ii := find(table, i);
      newtab[i] := HTValue(ht, ii);
      if newtab[i] = fail then
        newtab[i] := next;
        HTAdd(ht, ii, next);
        next := next + 1;
      fi;
    od;
    return newtab;
  end;
  colLookup := normalise(colLookup);
  rowLookup := normalise(rowLookup);

  # Make blocks
  colBlocks := List([1 .. Maximum(colLookup)], x -> []);
  rowBlocks := List([1 .. Maximum(rowLookup)], x -> []);
  for i in [1 .. Size(colLookup)] do
    Add(colBlocks[colLookup[i]], i);
  od;
  for u in [1 .. Size(rowLookup)] do
    Add(rowBlocks[rowLookup[u]], u);
  od;

  # Make n normal
  n := NormalClosure(g, n);

  cong := RZMSCongruenceByLinkedTriple(S, n, colBlocks, rowBlocks);
  SetGeneratingPairsOfMagmaCongruence(cong, pairs);
  return cong;
end);

_EquivalenceRelationCanonicalLookupRMS := function(cong)
  local S, n, elms, table, next, i, x;

  S := Range(cong);
  n := Size(S);
  elms := AsListCanonical(S);
  table := EmptyPlist(n);
  next := 1;
  for i in [1 .. n] do
    if not IsBound(table[i]) then
      for x in ImagesElm(cong, elms[i]) do
        table[PositionCanonical(S, x)] := next;
      od;
      next := next + 1;
    fi;
  od;
  return table;
end;

InstallMethod(EquivalenceRelationCanonicalLookup,
"for Rees matrix semigroup congruence by linked triple",
[IsRMSCongruenceByLinkedTriple],
_EquivalenceRelationCanonicalLookupRMS);

InstallMethod(EquivalenceRelationCanonicalLookup,
"for Rees 0-matrix semigroup congruence by linked triple",
[IsRZMSCongruenceByLinkedTriple],
_EquivalenceRelationCanonicalLookupRMS);

Unbind(_EquivalenceRelationCanonicalLookupRMS);
