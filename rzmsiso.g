# Given a Rees zero matrix semigroup returns a rees zero matrix semigroup with
# the same underlying group but created from a random matrix such that the
# returned semigroup is isomorphic to the input one.
RandomIsomorphicRZMS := function(S)
  local mat, m, n, T, G, out, x, i, j;
  mat := Matrix(S);
  m   := Length(mat);
  n   := Length(mat[1]);
  T   := [Random(SymmetricGroup(m)), Random(SymmetricGroup(n))];
  G   := UnderlyingSemigroup(S);
  Add(T, Random(AutomorphismGroup(G)));
  Add(T, List([1 .. m], i -> Random(G)));
  Add(T, List([1 .. n], i -> Random(G)));
  out := List([1 .. m], i -> EmptyPlist(n));
  for i in [1 .. m] do
    for j in [1 .. n] do
      x := mat[i ^ T[1]][j ^ T[2]];
      if x = 0 then
        out[i][j] := 0;
      else
        out[i][j] := (T[4][i]) * (x ^ T[3]) * (T[5][j] ^ -1);
      fi;
    od;
  od;
  return ReesZeroMatrixSemigroup(UnderlyingSemigroup(S), out);
end;

# Go from a triple in I x J x {1 .. |G| + 1} to an integer in
# [1 .. |I| * |J| * (|G| + 1)]. Inverse of Unflatten3DPoint.
Flatten3DPoint := function(dimensions, point)
  return (point[1] - 1) * dimensions[2] * dimensions[3] +
    (point[2] - 1) * dimensions[3] + (point[3] - 1) + 1;
end;

# Go from an integer in [1 .. |I| * |J| * (|G| + 1)] to an element of
# I x J x {1 .. |G| + 1}. Inverse of Flatten3DPoint.
Unflatten3DPoint := function(dimensions, value)
   local ret;
   ret    := [];
   value  := value - 1;
   ret[3] := value mod dimensions[3] + 1;
   value  := value - (ret[3] - 1);
   value  := value / dimensions[3];
   ret[2] := value mod dimensions[2] + 1;
   value  := value - (ret[2] - 1);
   ret[1] := value / dimensions[2] + 1;
   return ret;
end;

# Unflatten the entries of a set representing a matrix over a 0-group and return
# the corresponding matrix. Inverse of ZeroGroupMatrixToSet.
SetToZeroGroupMatrix := function(set, nr_rows, nr_cols, G)
  local 0G, mat, dim, point, x;
  0G  := Concatenation([0], Elements(G));
  mat := List([1 .. nr_rows], a -> EmptyPlist(nr_cols));
  dim := [nr_rows, nr_cols, Size(G) + 1];
  for x in set do
    point                   := Unflatten3DPoint(dim, x);
    mat[point[1]][point[2]] := 0G[point[3]];
  od;
  return mat;
end;

# Flatten the entries of a matrix over a 0-group and return as a set of
# integers. Inverse of SetToZeroGroupMatrix.
ZeroGroupMatrixToSet := function(mat, nr_rows, nr_cols, G)
  local set, dim, i, j;
  set := [];
  dim := [nr_rows, nr_cols, Size(G) + 1];
  for i in [1 .. nr_rows] do
    for j in [1 .. nr_cols] do
      if mat[i][j] = 0 then
        Add(set, Flatten3DPoint(dim, [i, j, 1]));
      else
        Add(set,
          Flatten3DPoint(dim, [i, j, 1 + Position(Elements(G),
                                              mat[i][j])]));
      fi;
    od;
  od;
  return set;
end;

# The representation of the group (G \wreath S_n) \rtimes Aut(G) acting on
# [1 .. |I| * |J| * (|G| + 1)] where the integers correspond to entries of a
# J x I matrix of a 0-group G.
RZMSMatrixIsomorphismGroup := function(nr_rows, nr_cols, G)
  local ApplyPermWholeDimension, ApplyPermSingleAssignDimension, dim, S, rows,
  cols, gens, elms, rmlt, grswaps, lmlt, gcswaps, auto;

  ApplyPermWholeDimension := function(dimensions, dim, perm)
    local map, point, i;
      map := [];
      for i in [1 .. Product(dimensions)] do
        point      := Unflatten3DPoint(dimensions, i);
        point[dim] := point[dim] ^ perm;
        map[i]     := Flatten3DPoint(dimensions, point);
      od;
    return PermList(map);
  end;

  ApplyPermSingleAssignDimension  := function(dimensions, dim,
                                              perm, fixdim, fixval)
    local map, point, i;
    map := [];
    for i in [1 .. Product(dimensions)] do
      point := Unflatten3DPoint(dimensions, i);
      if point[fixdim] = fixval then
        point[dim] := point[dim] ^ perm;
      fi;
      map[i] := Flatten3DPoint(dimensions, point);
    od;
    return PermList(map);
  end;

  dim := [nr_rows, nr_cols, Size(G) + 1];
  # Row Swaps
  S    := SymmetricGroup(nr_rows);
  rows := List(GeneratorsOfGroup(S),
               x -> ApplyPermWholeDimension(dim, 1, x));

  # Col swaps
  S    := SymmetricGroup(nr_cols);
  cols := List(GeneratorsOfGroup(S),
               x -> ApplyPermWholeDimension(dim, 2, x));

  gens := GeneratorsOfGroup(G);
  elms := ShallowCopy(Elements(G));

  # Apply g to each row (left multiplication by inverse):
  rmlt := List(gens, g -> PermList(Concatenation([1],
          1 + List(elms, e -> Position(elms, g ^ -1 * e)))));
  grswaps := List([1 .. dim[1]], r -> List(rmlt, g ->
  ApplyPermSingleAssignDimension(dim, 3, g, 1, r)));

  # Apply g to each col (right multiplication):
  lmlt := List(gens, g -> PermList(Concatenation([1],
          1 + List(elms, e -> Position(elms, e * g)))));
  gcswaps := List([1 .. dim[2]], r -> List(lmlt, g ->
  ApplyPermSingleAssignDimension(dim, 3, g, 2, r)));

  # Automorphisms of G
  S    := AutomorphismGroup(G);
  auto := List(GeneratorsOfGroup(S), x -> List(Elements(G), a ->
          Position(Elements(G), a ^ x)));
  Apply(auto, a -> PermList(Concatenation([1], a + 1)));
  auto := List(auto, x -> ApplyPermWholeDimension(dim, 3, x));

  # The RZMS matrix isomorphism group
  # TODO(CCR): maybe remove more generators here
  return Group(Flat([rows, cols, grswaps, gcswaps, auto]));
end;

IsomorphismReesZeroMatrixSemigroups := function(S, T)
  local mS, mT, m, n, GS, GT, grp_iso, grp_inv, setmS, func, mTT, setmT, GG,
  map, dimensions, pos, fun, invfun;

  mS := Matrix(S);
  mT := Matrix(T);

  m := Length(mS);
  n := Length(mS[1]);
  if not (Length(mT) = m and ForAll(mS, row -> Length(row) = n)
      and ForAll(mT, row -> Length(row) = n)) then
      # TODO(CCR): don't check all rows since the matrix must be m x n
    ErrorNoReturn("dimensions are different");
  fi;

  GS := UnderlyingSemigroup(S);
  GT := UnderlyingSemigroup(T);
  if not IsPermGroup(GS) or not IsPermGroup(GT) then
    ErrorNoReturn("the rzms should have underlying semigroups which are perm ",
                  "groups");
  fi;

  grp_iso := IsomorphismGroups(GS, GT);
  if grp_iso = fail then
    ErrorNoReturn("underlying groups are not isomorphic");
  fi;
  grp_inv := InverseGeneralMapping(grp_iso);

  # Each entry of a matrix corresponds to a triple (j, i, g) in J x I x G.
  # There is bijection between these triple and the set [1 .. |I| x |J| x G].
  # Here we turn a matrix into a set of integers which represent the entries of
  # the matrix. If the UnderlyingGroups of S and T are different then we map the
  # entries of the matrix of T into the group GS of S first.
  setmS := ZeroGroupMatrixToSet(mS, m, n, GS);
  func  := function(x)
    if x = 0 then
      return 0;
    fi;
    return x ^ grp_inv;
  end;
  mTT   := List(mT, row -> List(row, func));
  setmT := ZeroGroupMatrixToSet(mTT, m, n, GT);

  # We now find an element of (G \wreath S_n) \rtimes Aut(G) which sends the
  # martix of S to the matrix of T. We create the representation of this action
  # on the integers [1 .. |I| x |J| x G] to utilize permutation group methods.

  # JDM: Non-trivial amount of time
  GG  := RZMSMatrixIsomorphismGroup(m, n, GS);
  map := RepresentativeAction(GG, setmS, setmT, OnSets);

  dimensions := [m, n, Size(GS) + 1];

  pos := function(g)  # [i, j, 1] represents the (i,j)'th entry being 0.
    # Replace Elements -> Enumerator
    return Position(Elements(GS), g) + 1;
  end;

  # Note that Rees 0-martrix semigroup elements are triples in I x G x J,
  # whereas the matrix of a RZMS is a J x I matrix and it's entries are triples
  # in the set J x I x G.
  fun := function(x)
    local p;
    if x = MultiplicativeZero(S) then
      return MultiplicativeZero(T);
    fi;
    p := [x[3], x[1], pos(x[2] ^ -1)];
    p := Unflatten3DPoint(dimensions,
                          Flatten3DPoint(dimensions, p) ^ map);
    return ReesZeroMatrixSemigroupElement(T, p[2],
                                          (Elements(GS)[p[3] - 1] ^ -1)
                                          ^ grp_iso, p[1]);
  end;

  invfun := function(x)
    local p;
    if x = MultiplicativeZero(T) then
      return MultiplicativeZero(S);
    fi;
    p := [x[3], x[1], pos((x[2] ^ grp_inv) ^ -1)];
    p := Unflatten3DPoint(dimensions,
                          Flatten3DPoint(dimensions, p) ^ (map ^ -1));
    return ReesZeroMatrixSemigroupElement(S, p[2],
                                          Elements(GS)[p[3] - 1] ^ -1, p[1]);
  end;

  return MappingByFunction(S, T, fun, invfun);
end;
