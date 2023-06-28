################################
###   Monoid Cartan matrix   ###
################################

InstallMethod(MonoidCartanMatrix, "for a monoid", [IsMonoid],
function(S)
  local C, M;

  C := MonoidCharacterTable(S);
  M := RegularRepresentationBicharacter(S);

  return Inverse(TransposedMatMutable(C)) * M * Inverse(C);
end);

InstallMethod(TransversalIdempotents, "for a semigroup",
[IsSemigroup],
function(S)
  if not IsMonoidAsSemigroup(S) then
    ErrorNoReturn("the 1st argument (a semigroup) is not a monoid");
  fi;
  return List(List(RegularDClasses(S), GroupHClass), MultiplicativeNeutralElement);
end);

InstallMethod(SConjugacyClassReps, "for a semigroup", 
[IsSemigroup], 
function(S)
  local D, out, C, map;

  D := List(RegularDClasses(S), GroupHClass);
  D := List(D, IsomorphismPermGroup);
  out := [];
  for map in D do
    C := List(ConjugacyClasses(CharacterTable(Range(map))), Representative);
    # Ugly fix: ensures that the conjugacy classes are computed 
    # in the same order than for the group character table
    map := InverseGeneralMapping(map);
    C := List(C, x -> x ^ map);
    Append(out, C);
  od;
  return out;
end);

###############################################
###   Regular representation Bicharacter    ###
###############################################

# # To compare, simple fixed point counting
# DClassBicharacterNaive := function(S, D, C)
#   local c, M, i, j;
# 
#   c   := Length(C);
#   M   := List([1 .. c], x -> List([1 .. c], x -> 0));
# 
#   for i in [1 .. c] do
#     for j in [1 .. c] do
#       M[i][j] := Number(D, x -> C[i] * x * C[j] = x);
#     od;
#   od;
# 
#   return M;
# end;
# 
# # To compare, simple fixed point counting
# RegularRepresentationBicharacterNaive := function(S)
#   local C, c, M, i, j;
# 
#   C   := SConjugacyClassReps(S);
#   c   := Length(C);
#   M   := List([1 .. c], x -> List([1 .. c], x -> 0));
# 
#   for i in [1 .. c] do
#     for j in [1 .. c] do
#       M[i][j] := Number(S, s -> C[i] * s * C[j] = s);
#     od;
#   od;
# 
#   return M;
# end;
# 
# DClassBicharacter := function(S, D, C)
#   local G, cardG, CG, cG, cS, d, 
#         l_mults, lp_mults, l, lp, r_mults, rp_mults, r, rp,
#         LRec, RRec, h, k, i, j, g, pos, Diag;
# 
#   G   := SchutzenbergerGroup(D);
#   cardG := Size(G);
#   CG  := ConjugacyClasses(G);
#   cG  := Length(CG);
#   cS  := Length(C);
# 
#   d   := Representative(D);
# 
#   l_mults  := List(HClassReps(LClass(S, d)), h -> LeftGreensMultiplierNC(S, d, h));
#   lp_mults := List(HClassReps(LClass(S, d)), h -> LeftGreensMultiplierNC(S, h, d));
#   r_mults  := List(HClassReps(RClass(S, d)), h -> RightGreensMultiplierNC(S, d, h));
#   rp_mults := List(HClassReps(RClass(S, d)), h -> RightGreensMultiplierNC(S, h, d));
# 
#   LRec := List([1..cS], x -> List([1..cG], x -> 0));
# 
#   for i in [1 .. cS] do
#     h := C[i];
#     for j in [1..Length(l_mults)] do
#       l  := l_mults[j];
#       lp := lp_mults[j];
#       if h * l * d in RClass(S, l * d) then 
#         g := Inverse(LambdaPerm(S)(d, lp * h * l * d));
#         pos := Position(CG, ConjugacyClass(G, g));
#         LRec[i][pos] := LRec[i][pos] + 1;
#       fi;
#     od;
#   od;
# 
#   RRec := List([1..cG], x -> List([1..cS], x -> 0));
# 
#   for i in [1..cS] do
#     k := C[i];
#     for j in [1..Length(r_mults)] do
#       r  := r_mults[j];
#       rp := rp_mults[j];
#       if d * r * k in LClass(S, d * r) then
#         g   := LambdaPerm(S)(d, d * r * k * rp);
#         pos := Position(CG, ConjugacyClass(G, g));
#         RRec[pos][i] := RRec[pos][i] + 1;
#       fi;
#     od;
#   od;
#  
#   Diag := DiagonalMat(List(CG, x -> cardG / Size(x)));
#   return LRec * Diag * RRec;
# end;
# 
# ### Regular representation Bicharacter
# # DClassBicharacter iterated over all Dclasses of S.
# 
# RegularRepresentationBicharacter := function(S)
#   local C, D, c, mat, i, j;
# 
#   C := SConjugacyClassReps(S);
#   c := Length(C);
#   mat := List([1 .. c], x -> List([1 .. c], x -> 0));
# 
#   for D in DClasses(S) do
#     mat := mat + DClassBicharacter(S, D, C);
#   od;
# 
#   return mat;
# end;
# 
# #############################
# ###   L-class character   ###
# #############################
# 
# # To compare, simple fixed point counting
# LClassBicharacterNaive := function(S, e, CS)
#   local cS, CG, cG, M, i, j;
# 
#   cS := Length(CS);
#   CG := Filtered(CS, c -> c in HClass(S, e));
#   cG := Length(CG);
#   M := List([1 .. cS], x -> List([1 .. cG], x -> 0));
# 
#   for i in [1 .. cS] do
#     for j in [1 .. cG] do
#       M[i][j] := Number(LClass(S, e), l -> CS[i] * l * CG[j] = l);
#     od;
#   od;
# 
#   return TransposedMatMutable(M);
# end;
# 
# # Assumes e is in CS
# LClassBicharacter := function(S, e, CS)
#   local H, map, HH, l_mults, lp_mults,
#         cS, CG, cG, M, CHH, CardCentralizer,
#         i, j, k, l, lp, y, c;
# 
#   H   := HClass(S, e);
#   map := IsomorphismPermGroup(H);
#   HH  := Range(map);
# 
#   l_mults := List(HClassReps(LClass(S, e)), h -> LeftGreensMultiplierNC(S, e, h) * e);
#   lp_mults     := List(HClassReps(LClass(S, e)), h -> e * LeftGreensMultiplierNC(S, h, e));
# 
#   cS   := Length(CS);
#   CG   := Filtered(CS, x -> x in HClass(S, e));;
#   cG   := Length(CG);
#   M    := List([1 .. cG], x -> List([1 .. cS], x -> 0));
# 
#   CHH      := ConjugacyClasses(HH);
#   CardCentralizer := List(CG, c -> CentralizerOrder(HH, c^map));
# 
#   for j in [1 .. cS] do
#       for k in [1 .. Length(l_mults)] do
#         l  := l_mults[k];
#         lp := lp_mults[k];
#         if CS[j] * l * e in HClass(S, l * e) then
#           y := Inverse((lp * CS[j] * l * e)^map);
#           c := ConjugacyClass(HH, y);
#           i := Position(CHH, c);
#           M[i][j] := M[i][j] + CardCentralizer[i];
#         fi;
#       od;
#   od;
# 
#   return M;
# end;
# 
# ConcatenatedLClassBicharacters := function(S)
#   local M, C, e;
# 
#   M := [];
#   C := SConjugacyClassReps(S);
#   for e in TransversalIdempotents(S) do
#     M := Concatenation(M, LClassBicharacter(S, e, C));
#   od;
# 
#   return M;
# end;
# 
# #############################
# ###   R-class character   ###
# ############################# 
# 
# RClassBicharacterNaive := function(S, e, CS)
#   local cS, CG, cG, M, i, j;
# 
#   cS := Length(CS);
#   CG := Filtered(CS, c -> c in HClass(S, e));
#   cG := Length(CG);
#   M := List([1 .. cG], x -> List([1 .. cS], x -> 0));
# 
#   for i in [1 .. cG] do
#     for j in [1 .. cS] do
#       M[i][j] := Number(RClass(S, e), r -> CG[i] * r * CS[j] = r);
#     od;
#   od;
# 
#   return M;
# end;
# 
# RClassBicharacter := function(S, e, CS)
#   local H, map, HH, r_mults, rp_mults,
#         cS, CG, cG, M, CHH, CardCentralizer,
#         i, j, k, r, rp, y, c;
# 
#   H   := HClass(S, e);
#   map := IsomorphismPermGroup(H);
#   HH  := Range(map);
# 
#   r_mults := List(HClassReps(RClass(S, e)), h -> RightGreensMultiplierNC(S, e, h));
#   rp_mults     := List(HClassReps(RClass(S, e)), h -> RightGreensMultiplierNC(S, h, e));
# 
#   cS   := Length(CS);
#   CG   := Filtered(CS, x -> x in HClass(S, e));;
#   cG   := Length(CG);
#   M    := List([1 .. cG], x -> List([1 .. cS], x -> 0));
# 
#   CHH      := ConjugacyClasses(HH);
#   CardCentralizer := List(CG, c -> CentralizerOrder(HH, c^map));
# 
#   for j in [1 .. cS] do
#       for k in [1 .. Length(r_mults)] do
#         r  := r_mults[k];
#         rp := rp_mults[k];
#         if e * r * CS[j] in HClass(S, e * r) then
#           y := Inverse((e * r * CS[j] * rp)^map);
#           c := ConjugacyClass(HH, y);
#           i := Position(CHH, c);
#           M[i][j] := M[i][j] + CardCentralizer[i];
#         fi;
#       od;
#   od;
# 
#   return M;
# end;
# 
# ConcatenatedRClassBicharacters := function(S)
#   local M, C, e;
# 
#   M := [];
#   C := SConjugacyClassReps(S);
#   for e in TransversalIdempotents(S) do
#     M := Concatenation(M, RClassBicharacter(S, e, C));
#   od;
# 
#   return M;
# end;
