############################################################################
##
##  congruences/conginv.gi
##  Copyright (C) 2015-2022                               Michael C. Young
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
## This file contains methods for congruences on inverse semigroups, using the
## "kernel and trace" representation.
##
## See J.M. Howie's "Fundamentals of Semigroup Theory" Section 5.3, and see
## Michael Young's MSc thesis "Computing with Semigroup Congruences" Chapter 5
## (www-circa.mcs.st-and.ac.uk/~mct25/files/mt5099-report.pdf) for more details.
##

# TODO:
# * handle semilattices

# FIXME this shouldn't be necessary, it's a direct copy of the method for
# CanComputeEquivalenceRelationPartition, but is here so that the method has a
# higher rank
InstallMethod(EquivalenceClasses,
"for an inverse semigroup congruence by kernel and trace",
[IsInverseSemigroupCongruenceByKernelTrace],
function(C)
  local part, classes, i;
  part := EquivalenceRelationPartitionWithSingletons(C);
  classes := [];
  for i in [1 .. Length(part)] do
    classes[i] := EquivalenceClassOfElementNC(C, part[i][1]);
    SetAsList(classes[i], part[i]);
  od;
  return classes;
end);

InstallGlobalFunction(InverseSemigroupCongruenceByKernelTrace,
function(S, kernel, trace)
  local a, traceClass, f, l, e;
  if not IsInverseSemigroup(S)
      and IsMultiplicativeElementWithInverseCollection(S) then
    ErrorNoReturn("the 1st argument is not an inverse ",
                  "semigroup with inverse op");
  elif not IsInverseSubsemigroup(S, kernel) then
    # Check that the kernel is an inverse subsemigroup
    ErrorNoReturn("the 2nd argument is not an inverse ",
                  "subsemigroup of the 1st argument (an inverse semigroup)");
  elif NrIdempotents(kernel) <> NrIdempotents(S) then
    # (1) Must contain all the idempotents of S
    ErrorNoReturn("the 2nd argument (an inverse semigroup) does not contain ",
                  "all of the idempotents of the 1st argument (an inverse",
                  " semigroup)");
  elif not IsNormalInverseSubsemigroup(S, kernel) then
    # (2) Must be self-conjugate
    ErrorNoReturn("the 2nd argument (an inverse semigroup) must be ",
                  "a normal inverse subsemigroup of the 1st argument (an ",
                  "inverse semigroup)");
  fi;

  if not IsSemigroupCongruence(trace) then
    ErrorNoReturn("the 3rd argument must be a 2-sided congruence");
  elif Source(trace) <> IdempotentGeneratedSubsemigroup(S) then
    ErrorNoReturn("the 3rd argument must be a 2-sided congruence of the ",
                  "semilattice of idempotents of the 1st argument");
  elif not IsNormalCongruence(S, trace) then
    ErrorNoReturn("the 3rd argument must be a normal 2-sided congruence of ",
                  "the semilattice of idempotents of the 1st argument, found a",
                  " non-normal congruence");
  fi;

  # Check conditions for a congruence pair: Howie p.156
  for traceClass in EquivalenceClasses(trace) do
    for f in traceClass do
      l := LClass(S, f);
      for a in l do
        if a in kernel then
          # Condition (C2): aa' related to a'a
          if not LeftOne(a) in traceClass then
            ErrorNoReturn("not a valid congruence pair (C2)");
          fi;
        else
          # Condition (C1): (ae in kernel && e related to a'a) => a in kernel
          for e in traceClass do
            if a * e in kernel then
              ErrorNoReturn("not a valid congruence pair (C1)");
            fi;
          od;
        fi;
      od;
    od;
  od;
  return InverseSemigroupCongruenceByKernelTraceNC(S, kernel, trace);
end);

InstallGlobalFunction(InverseSemigroupCongruenceByKernelTraceNC,
function(S, kernel, trace)
  local fam, C;

  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                               ElementsFamily(FamilyObj(S)));
  C := Objectify(NewType(fam, IsInverseSemigroupCongruenceByKernelTrace),
                 rec());
  SetSource(C, S);
  SetRange(C, S);
  SetKernelOfSemigroupCongruence(C, kernel);
  SetTraceOfSemigroupCongruence(C, trace);
  return C;
end);

InstallMethod(ViewObj,
"for inverse semigroup congruence by kernel and trace",
[IsInverseSemigroupCongruenceByKernelTrace],
function(C)
  Print("<2-sided semigroup congruence over ");
  ViewObj(Range(C));
  PrintFormatted(" with congruence pair ({},{})>",
                 Size(KernelOfSemigroupCongruence(C)),
                 NrEquivalenceClasses(TraceOfSemigroupCongruence(C)));
  return;
end);

InstallMethod(\=,
"for two inverse semigroup congruences by kernel and trace",
[IsInverseSemigroupCongruenceByKernelTrace,
 IsInverseSemigroupCongruenceByKernelTrace],
function(lhop, rhop)
  return (Range(lhop) = Range(rhop)
          and KernelOfSemigroupCongruence(lhop)
            = KernelOfSemigroupCongruence(rhop)
          and TraceOfSemigroupCongruence(lhop)
            = TraceOfSemigroupCongruence(rhop));
end);

InstallMethod(IsSubrelation,
"for two inverse semigroup congruences by kernel and trace",
[IsInverseSemigroupCongruenceByKernelTrace,
 IsInverseSemigroupCongruenceByKernelTrace],
function(lhop, rhop)
  # Tests whether rhop is a subcongruence of lhop
  if Range(lhop) <> Range(rhop) then
    Error("the 1st and 2nd arguments are congruences over different",
          " semigroups");
  fi;
  return IsSubsemigroup(KernelOfSemigroupCongruence(lhop),
                        KernelOfSemigroupCongruence(rhop))
         and IsSubrelation(TraceOfSemigroupCongruence(lhop),
                           TraceOfSemigroupCongruence(rhop));
end);

InstallMethod(ImagesElm,
"for inverse semigroup congruence by kernel and trace and mult. elt.",
[IsInverseSemigroupCongruenceByKernelTrace,
 IsMultiplicativeElementWithInverse],
function(C, a)
  local S, T, data, o, i, j, m, aa, rep, l, g, gg, Pi, Pj, lookup, result, preim, lmult, rmult;

  S := Source(C);
  if not a in S then
    ErrorNoReturn("the 2nd argument (a mult. elt. with inverse) does not ",
                  "belong to the source of the 1st argument (a congruence)");
  fi;

  T    := TraceOfSemigroupCongruence(C);
  data := InverseSemigroupQuotientData(C);

  o  := LambdaOrb(S);
  i  := Position(o, LambdaFunc(S)(a));
  j  := Position(o, RhoFunc(S)(a));
  m  := OrbSCCLookup(o)[i];
  aa := LambdaOrbMult(o, m, j)[1] * a * LambdaOrbMult(o, m, i)[2];

  rep := LambdaOrbRep(o, m);
  l   := Position(o, RhoFunc(S)(rep));
  rep := LambdaOrbMult(LambdaOrb(S), m, l)[1] * rep;

  g := LambdaPerm(S)(rep, aa);
  gg := g ^ data.all_homs[m];

  Pi := EquivalenceClassOfElementNC(T, PartialPerm(o[i], o[i]));
  Pi := List(Pi, x -> Position(o, ImageSetOfPartialPerm(x)));

  Pj := EquivalenceClassOfElementNC(T, PartialPerm(o[j], o[j]));
  Pj := List(Pj, x -> Position(o, ImageSetOfPartialPerm(x)));
  lookup := OrbSCCLookup(o);

  result := [];

  for i in Pi do
    for j in Pj do
      if lookup[i] = lookup[j] then
        m := lookup[i];
        if gg in ImagesSource(data.all_homs[m]) then
          preim := PreImagesElm(data.all_homs[m], gg);
          lmult := LambdaOrbMult(o, m, j)[2];
          rmult := LambdaOrbMult(o, m, i)[1];
          rep   := RightOne(LambdaOrbRep(o, m));
          Append(result, List(preim, x -> lmult * rep * x * rmult));
        fi;
      fi;
    od;
  od;
  return result;
end);

# TODO check if this is necessary
InstallMethod(PreImagesElm,
"for inverse semigroup congruence by kernel and trace and mult. elt.",
[IsInverseSemigroupCongruenceByKernelTrace,
 IsEquivalenceClass],
function(C, a)
  # TODO check that the equiv. class belongs to the correct semigroup
  return ImagesElm(C, Representative(a));
end);


InstallMethod(EquivalenceRelationPartitionWithSingletons,
"for inverse semigroup congruence by kernel and trace",
[IsInverseSemigroupCongruenceByKernelTrace],
function(C)
  local data, T, o, comps, result, comp, G, i, j, Pi, Pj, lookup, next, m, preim, lmult, rmult, rep, mm, ii, jj, gg;

  # FIXME this should be sufficient but isn't because taking the quotient is
  # super slow, so the fixme is to not make taking the quotient slow, and to
  # then remove the extra code below.
  # return List(Source(C) / C, x -> PreImagesElm(C, x));

  data := InverseSemigroupQuotientData(C);
  T := TraceOfSemigroupCongruence(C);
  o := LambdaOrb(Source(C));
  comps := DigraphStronglyConnectedComponents(data.graph).comps;
  result := [];
  for mm in [1 .. Length(comps)] do
    comp := comps[mm];
    if comp = [1] then
      continue;
    fi;
    G := Range(data.rep_homs[mm]); # TODO maybe ImagesSourc?
    for ii in comp do
      i := Position(data.graph_hom, ii, 1);
      for jj in comp do
        j := Position(data.graph_hom, jj, 1);
        for gg in G do
          Pi := EquivalenceClassOfElementNC(T, PartialPerm(o[i], o[i]));
          Pi := List(Pi, x -> Position(o, ImageSetOfPartialPerm(x)));

          Pj := EquivalenceClassOfElementNC(T, PartialPerm(o[j], o[j]));
          Pj := List(Pj, x -> Position(o, ImageSetOfPartialPerm(x)));
          lookup := OrbSCCLookup(o);
          next := [];

          for i in Pi do
            for j in Pj do
              if lookup[i] = lookup[j] then
                m := lookup[i];
                if gg in ImagesSource(data.all_homs[m]) then
                  preim := PreImagesElm(data.all_homs[m], gg);
                  lmult := LambdaOrbMult(o, m, i)[2];
                  rmult := LambdaOrbMult(o, m, j)[1];
                  rep   := RightOne(LambdaOrbRep(o, m));
                  Append(next, List(preim, x -> lmult * rep * x * rmult));
                fi;
              fi;
            od;
          od;
          Add(result, next);
        od;
      od;
    od;
  od;
  return result;
end);

# TODO only works for partial perm semigroups

InstallMethod(NrEquivalenceClasses,
"for inverse semigroup congruence by kernel and trace",
[IsInverseSemigroupCongruenceByKernelTrace],
function(C)
  local K, T, o, D, parts, node_parts, Q, scc, result, x, HS, HK, part, comp;

  if HasEquivalenceRelationPartitionWithSingletons(C) then
    return Size(EquivalenceRelationPartitionWithSingletons(C));
  elif IsSemilattice(Source(C)) then
    # This is required because IsSemilattice => not IsActingSemigroup
    # and so LambdaOrb errors below.
    return NrEquivalenceClasses(TraceOfSemigroupCongruence(C));
  fi;

  K := KernelOfSemigroupCongruence(C);
  T := TraceOfSemigroupCongruence(C);
  o := LambdaOrb(Source(C));

  D := StructuralCopy(OrbitGraph(o)) - 1;
  Remove(D, 1);
  D := DigraphNC(D);

  parts := EquivalenceRelationPartitionWithSingletons(T);
  node_parts := [];
  for part in parts do
    Add(node_parts,
        List(part, x -> Position(o, ImageSetOfPartialPerm(x)) - 1));
  od;

  Q   := QuotientDigraph(D, node_parts);
  scc := DigraphStronglyConnectedComponents(Q).comps;

  result := 0;
  for comp in scc do
    x := MeetOfPartialPerms(parts[comp[1]]);
    HS := HClass(Source(C), x);
    HK := HClass(K, x);
    result := result + Size(comp) ^ 2 * (Size(HS) / Size(HK));
  od;

  return result;
end);

InstallMethod(CongruenceTestMembershipNC,
"for inverse semigroup congruence by kernel and trace and two mult. elts",
[IsInverseSemigroupCongruenceByKernelTrace,
 IsMultiplicativeElement,
 IsMultiplicativeElement],
function(C, x, y)
  return CongruenceTestMembershipNC(TraceOfSemigroupCongruence(C),
                                    LeftOne(x),
                                    LeftOne(y))
         and x / y in KernelOfSemigroupCongruence(C);
end);

InstallMethod(EquivalenceClassOfElementNC,
"for inverse semigroup congruence by kernel and trace and mult. elt.",
[IsInverseSemigroupCongruenceByKernelTrace, IsMultiplicativeElement],
function(C, x)
  local class;
  class := Objectify(InverseSemigroupCongruenceClassByKernelTraceType(C),
                     rec());
  SetParentAttr(class, Range(C));
  SetEquivalenceClassRelation(class, C);
  SetRepresentative(class, x);
  return class;
end);

InstallMethod(InverseSemigroupCongruenceClassByKernelTraceType,
"for inverse semigroup congruence by kernel and trace",
[IsInverseSemigroupCongruenceByKernelTrace],
function(C)
  return NewType(FamilyObj(Range(C)),
                 IsInverseSemigroupCongruenceClassByKernelTrace);
end);

InstallMethod(TraceOfSemigroupCongruence, "for semigroup congruence",
[IsSemigroupCongruence],
function(C)
  local S, copy;

  S := Range(C);
  if not (IsInverseSemigroup(S) and IsGeneratorsOfInverseSemigroup(S)) then
    ErrorNoReturn("the range of the argument (a congruence) must be an ",
                  "inverse semigroup with inverse op");
  fi;
  copy := AsInverseSemigroupCongruenceByKernelTrace(C);
  return TraceOfSemigroupCongruence(copy);
end);

InstallMethod(KernelOfSemigroupCongruence, "for semigroup congruence",
[IsSemigroupCongruence],
function(C)
  local S, copy;
  S := Range(C);
  if not (IsInverseSemigroup(S) and IsGeneratorsOfInverseSemigroup(S)) then
    ErrorNoReturn("the range of the argument (a congruence) must be an ",
                  "inverse semigroup with inverse op");
  fi;
  copy := AsInverseSemigroupCongruenceByKernelTrace(C);
  return KernelOfSemigroupCongruence(copy);
end);

InstallMethod(AsInverseSemigroupCongruenceByKernelTrace,
"for semigroup congruence with generating pairs",
[IsUniversalSemigroupCongruence],
function(C)
  local S, trace;
  S := Range(C);
  if not (IsInverseSemigroup(S) and IsGeneratorsOfInverseSemigroup(S)) then
    ErrorNoReturn("the range of the argument (a congruence) must be an ",
                  "inverse semigroup with inverse op");
  fi;
  trace := UniversalSemigroupCongruence(IdempotentGeneratedSubsemigroup(S));
  return InverseSemigroupCongruenceByKernelTraceNC(S, S, trace);
end);

InstallMethod(AsInverseSemigroupCongruenceByKernelTrace,
"for semigroup congruence with generating pairs",
[IsSemigroupCongruence and HasGeneratingPairsOfMagmaCongruence],
function(C)
  local S, kernel, trace, T, pairs, result;

  S := Source(C);
  if not (IsInverseSemigroup(S) and IsGeneratorsOfInverseSemigroup(S)) then
    ErrorNoReturn("the range of the argument (a congruence) must be an ",
                  "inverse semigroup with inverse op");
  elif HasKernelOfSemigroupCongruence(C)
      and HasTraceOfSemigroupCongruence(C) then
    kernel := KernelOfSemigroupCongruence(C);
    trace := TraceOfSemigroupCongruence(C);
    return InverseSemigroupCongruenceByKernelTraceNC(S, kernel, trace);
  fi;
  # TODO handle semilattices?
  T      := IdempotentGeneratedSubsemigroup(S);
  trace  := SemigroupCongruenceByGeneratingPairs(T, []);
  pairs  := GeneratingPairsOfSemigroupCongruence(C);
  result := SEMIGROUPS.KernelTraceClosure(S, T, trace, pairs);
  SetGeneratingPairsOfMagmaCongruence(result, pairs);
  return result;
end);

InstallMethod(JoinSemigroupCongruences,
"for inverse semigroup congruence",
[IsInverseSemigroupCongruenceByKernelTrace,
 IsInverseSemigroupCongruenceByKernelTrace],
function(lhop, rhop)
  local lker, rker, kernel, ltrace, rtrace, trace;

  if Source(lhop) <> Source(rhop) then
    Error("cannot form the join of congruences over different semigroups");
  fi;

  lker := KernelOfSemigroupCongruence(lhop);
  rker := KernelOfSemigroupCongruence(rhop);

  # kernel generated by union of lhop's kernel and rhop's kernel
  kernel := InverseSemigroup(GeneratorsOfInverseSemigroup(lker),
                             GeneratorsOfInverseSemigroup(rker),
                             rec(small := true));

  ltrace := TraceOfSemigroupCongruence(lhop);
  rtrace := TraceOfSemigroupCongruence(rhop);

  # trace is join of lhop's trace and rhop's trace
  trace := JoinSemigroupCongruences(ltrace, rtrace);

  return SEMIGROUPS.KernelTraceClosure(Source(lhop), kernel, trace, []);
end);

InstallMethod(MeetSemigroupCongruences,
"for two inverse semigroup congruence",
[IsInverseSemigroupCongruenceByKernelTrace,
 IsInverseSemigroupCongruenceByKernelTrace],
function(lhop, rhop)
  local lker, rker, gens, kernel, ltrace, rtrace, trace;

  if Source(lhop) <> Source(rhop) then
    Error("cannot form the meet of congruences over different semigroups");
  fi;

  lker := KernelOfSemigroupCongruence(lhop);
  rker := KernelOfSemigroupCongruence(rhop);
  gens := SmallInverseSemigroupGeneratingSet(Intersection(lker, rker));
  kernel := InverseSemigroup(gens);

  ltrace := TraceOfSemigroupCongruence(lhop);
  rtrace := TraceOfSemigroupCongruence(rhop);

  trace := MeetSemigroupCongruences(ltrace, rtrace);

  return InverseSemigroupCongruenceByKernelTrace(Source(lhop), kernel, trace);
end);

# TODO this only works for partial perms

SEMIGROUPS.KernelTraceClosure := function(S, kernel, trace, genpairs)
  local kernel_gens_to_add, trace_pairs_to_add, x, enumerate_trace, pair,
  enforce_conditions, y;

  # This function takes an inverse semigroup S, a subsemigroup ker, an
  # equivalence traceBlocks on the idempotents, and a list of pairs in S.
  # It returns the minimal congruence containing "kernel" in its kernel and
  # "trace" in its trace, and containing all the given pairs

  kernel := InverseSubsemigroup(S, kernel);
  kernel_gens_to_add := Set(genpairs, x -> x[1] / x[2]);

  trace_pairs_to_add := List(genpairs, x -> [RightOne(x[1]), RightOne(x[2])]);
  AsListCanonical(S);  # makes the computation below somewhat faster

  # TODO HERE pull this out, after refactoring to call this something like
  # "NormalCongruence" and actually passing the arguments instead of global
  # variables.
  enumerate_trace := function()
    local pairs, pair, a, x, y;
    Assert(0, IsNormalCongruence(S, trace));
    trace_pairs_to_add := Set(trace_pairs_to_add);
    for pair in trace_pairs_to_add do
      if not CongruenceTestMembershipNC(trace, pair[1], pair[2]) then
        pairs := ShallowCopy(GeneratingPairsOfSemigroupCongruence(trace));
        Add(pairs, pair);
        trace := SemigroupCongruenceByGeneratingPairs(Source(trace), pairs);
      fi;
      for a in GeneratorsOfSemigroup(S) do
        x := pair[1] ^ a;
        y := pair[2] ^ a;
        if not CongruenceTestMembershipNC(trace, x, y) then
          Add(trace_pairs_to_add, [x, y]);
        fi;
      od;
    od;
    Assert(0, IsNormalCongruence(S, trace));
    trace_pairs_to_add := [];
  end;

  enforce_conditions := function()
    local e, f, enum, D, i, j, a;

    # C2 condition
    for D in DClasses(kernel) do
      for i in [1 .. NrIdempotents(D) - 1] do
        e := Idempotents(D)[i];
        for j in [i + 1 .. NrIdempotents(D)] do
          f := Idempotents(D)[j];
          if not CongruenceTestMembershipNC(trace, e, f) then
            Add(trace_pairs_to_add, Set([e, f]));
          fi;
        od;
      od;
    od;
    if not IsEmpty(trace_pairs_to_add) then
      return;
    fi;

    enum := EnumeratorCanonical(kernel);
    for a in EnumeratorCanonical(S) do
      if not a in enum then
        e := MeetOfPartialPerms(ImagesElm(trace, RightOne(a)));
        # C1 condition
        if a * e in enum then
          AddSet(kernel_gens_to_add, a);
          if Size(kernel_gens_to_add) >= 128 then
            return;
          fi;
        fi;
      fi;
    od;
  end;

  repeat
    enumerate_trace();
    # Take the normal closure inverse semigroup containing the new elements
    kernel := NormalClosureInverseSemigroupNC(S,
                                              kernel,
                                              kernel_gens_to_add);
    kernel_gens_to_add := [];
    enforce_conditions();
  until IsEmpty(kernel_gens_to_add) and IsEmpty(trace_pairs_to_add);

  return InverseSemigroupCongruenceByKernelTraceNC(S, kernel, trace);
end;

########################################################################

# The maximum congruence whose quotient is a group
InstallMethod(MinimumGroupCongruence,
"for an inverse semigroup with inverse op",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup],
function(S)
  local ker, trace;

  ker := MajorantClosureNC(S, Idempotents(S));
  ker := InverseSemigroup(SmallInverseSemigroupGeneratingSet(ker));
  trace := UniversalSemigroupCongruence(IdempotentGeneratedSubsemigroup(S));

  return InverseSemigroupCongruenceByKernelTraceNC(S, ker, trace);
end);

InstallMethod(MaximumIdempotentSeparatingCongruence,
"for an acting partial perm semigroup",
[IsPartialPermSemigroup and IsActingSemigroup and IsInverseSemigroup],
function(S)
  local ker, trace;

  ker := CentralizerOfIdempotents(S);
  trace := TrivialCongruence(IdempotentGeneratedSubsemigroup(S));

  return InverseSemigroupCongruenceByKernelTraceNC(S, ker, trace);
end);

# TODO(later) this is a completely generic version implementation, maybe move
# this elsewhere?

InstallMethod(GeneratingPairsOfMagmaCongruence,
"for inverse semigroup congruence by kernel and trace",
[IsInverseSemigroupCongruenceByKernelTrace],
function(C)
  local pairs, CC, class, i;

  pairs := [];
  CC := SemigroupCongruenceByGeneratingPairs(Source(C), pairs);
  for class in EquivalenceRelationPartition(C) do
    for i in [2 .. Length(class)] do
      if not CongruenceTestMembershipNC(CC, class[i], class[1]) then
        pairs := GeneratingPairsOfSemigroupCongruence(CC);
        pairs := Concatenation(pairs, [[class[i], class[1]]]);
        CC := SemigroupCongruenceByGeneratingPairs(Source(C), pairs);
        if NrEquivalenceClasses(CC) = NrEquivalenceClasses(C) then
          return pairs;
        fi;
      fi;
    od;
  od;
  return pairs;
end);

InstallMethod(IsIdempotentPureCongruence,
"for inverse semigroup congruence by kernel and trace",
[IsInverseSemigroupCongruenceByKernelTrace],
function(C)
  return Size(KernelOfSemigroupCongruence(C)) = NrIdempotents(Range(C));
end);

InstallMethod(IsIdempotentPureCongruence, "for a semigroup congruence",
[IsSemigroupCongruence],
function(C)
  local e;

  if not IsInverseSemigroup(C) then
    ErrorNoReturn("TODO");
  elif IsSemilattice(Source(C)) then
    return true;
  elif HasKernelOfSemigroupCongruence(C)
      and HasTraceOfSemigroupCongruence(C) then
    C := AsInverseSemigroupCongruenceByKernelTrace(C);
    return IsIdempotentPureCongruence(C);
  fi;

  for e in Idempotents(Source(C)) do
    if ForAny(EquivalenceClassOfElementNC(C, e), x -> not IsIdempotent(x)) then
      return false;
    fi;
  od;
  return true;
end);

InstallMethod(IsNormalCongruence,
"for an inverse semigroup and congruence",
[IsInverseSemigroup, IsSemigroupCongruence],
function(S, C)
  local A, P, p, a;

  if not IsInverseSubsemigroup(S, Source(C)) then
    ErrorNoReturn("the source of the 2nd argument (a congruence) is not an",
                  " inverse subsemigroup of the 1st argument (an inverse",
                  " semigroup)");
  fi;

  A := GeneratorsOfSemigroup(S);
  P := GeneratingPairsOfSemigroupCongruence(C);
  for p in P do
    for a in A do
      if not CongruenceTestMembershipNC(C, p[1] ^ a, p[2] ^ a) then
        return false;
      fi;
    od;
  od;
  return true;
end);

InstallMethod(PrincipalNormalCongruencesIdempotentSemilattice,
"for an inverse semigroup", [IsInverseSemigroup],
function(S)
  local T, princ;
  # Every normal congruence C on the semilattice of idempotents is the
  # trace of a congruence on S, and if not the trivial congruence, then
  # there exist a pair of idempotents related in C. Hence the below captures
  # all of the principal normal congruences.
  T := IdempotentGeneratedSubsemigroup(S);
  # TODO(later) could pass the Combinations(AsList(T), 2) through the
  # GeneratingPairsOfPrincipalCongruences machinery
  princ := PrincipalCongruencesOfSemigroup(S, Combinations(AsList(T), 2));
  return List(princ, TraceOfSemigroupCongruence);
end);

InstallMethod(NormalCongruencesIdempotentSemilattice,
"for an inverse semigroup", [IsInverseSemigroup],
function(S)
  local princ;
  princ := ShallowCopy(PrincipalNormalCongruencesIdempotentSemilattice(S));
  Add(princ, TrivialCongruence(IdempotentGeneratedSubsemigroup(S)));
  # The join of normal congruences is normal.
  return JoinSemilatticeOfCongruences(princ);
end);

InstallMethod(PrincipalIdempotentPureCongruences,
"for an inverse semigroup", [IsInverseSemigroup],
function(S)
  local T, princ;
  # Every idempotent pure congruence is the join of principal idempotent pure
  # congruences, i.e. those congruences where the kernel is just E(S). So we do
  # the same as above.
  T := IdempotentGeneratedSubsemigroup(S);
  # TODO(later) could pass the Combinations(AsList(T), 2) through the
  # GeneratingPairsOfPrincipalCongruences machinery
  princ := PrincipalCongruencesOfSemigroup(S, Combinations(AsList(T), 2));
  return Filtered(princ, x -> KernelOfSemigroupCongruence(x) = T);
end);

InstallMethod(IdempotentPureCongruences,
"for an inverse semigroup", [IsInverseSemigroup],
function(S)
  local princ;
  princ := ShallowCopy(PrincipalIdempotentPureCongruences(S));
  Add(princ, TrivialCongruence(IdempotentGeneratedSubsemigroup(S)));
  return JoinSemilatticeOfCongruences(princ);
end);

InstallMethod(SyntacticCongruence,
"for an inverse semigroup", [IsInverseSemigroup],
function(S)
  local princ;
  # The syntactic congruence is the join of the idempotent pure congruences,
  # i.e. those congruences where the kernel is just E(S).
  princ := PrincipalIdempotentPureCongruences(S);
  if IsEmpty(princ) then
    return TrivialCongruence(S);
  fi;
  return JoinSemigroupCongruences(princ);
end);

QuotientWordGraphNC := function(D, lookup)
  local result, nbs, n, s, t, v, e;

  result := [];
  nbs := OutNeighbours(D);
  n := Length(nbs[1]);
  Assert(1, ForAll(nbs, x -> Length(x) = n));
  for v in DigraphVertices(D) do
    for e in [1 .. n] do
      s := lookup[v];
      t := lookup[nbs[v][e]];
      if not IsBound(result[s]) then
        result[s] := [];
      fi;
      if not IsBound(result[s][e]) then
        result[s][e] := t;
      elif result[s][e] <> t then
        Error("The partition is not invariant!");
      fi;
    od;
  od;
  return DigraphNC(result);
end;


InstallMethod(InverseSemigroupQuotientData,
"for an inverse semigroup congruence by kernel + trace",
[IsInverseSemigroupCongruenceByKernelTrace],
function(C)
  local result, K, T, o, D, parts, hom, i, node_part, quotient_scc, scc, lookup, mm, x, l, m, G, N, map, gens, y, p, dom, imgs, ghom, part, comp;

  result := rec();
  K := KernelOfSemigroupCongruence(C);
  T := TraceOfSemigroupCongruence(C);
  o := LambdaOrb(Source(C));

  D := StructuralCopy(OrbitGraph(o));
  D := DigraphNC(D);
  parts := EquivalenceRelationPartitionWithSingletons(T);

  hom := [1];
  i := 1;
  for part in parts do
    i := i + 1;
    node_part := List(part, x -> Position(o, ImageSetOfPartialPerm(x)));
    # hom is not the same as lookup
    hom{node_part} := ListWithIdenticalEntries(Size(part), i);
  od;

  result.graph  := QuotientWordGraphNC(D, hom);
  result.graph_hom := hom;
  result.rep_homs := [];
  result.all_homs  := [];
  result.reps := [];
  result.reps_pos := [];

  quotient_scc := DigraphStronglyConnectedComponents(result.graph);
  scc := OrbSCC(o);
  lookup := OrbSCCLookup(o);

  for comp in quotient_scc.comps do
    if comp = [1] then continue; fi;
    x := MeetOfPartialPerms(parts[comp[1] - 1]);
    l := Position(o, ImageSetOfPartialPerm(x));
    m := lookup[l];
    x := LambdaOrbMult(o, m, l)[1] * x * LambdaOrbMult(o, m, l)[2];

    mm := quotient_scc.id[comp[1]];
    result.reps[mm]     := x;
    result.reps_pos[mm] := hom[scc[m][1]];
    Assert(1, quotient_scc.id[hom[scc[m][1]]] = mm);
    G := SchutzenbergerGroup(HClass(Source(C), x));
    N := SchutzenbergerGroup(HClass(K, x));
    map := NaturalHomomorphismByNormalSubgroup(G, N);
    result.rep_homs[mm] := map;
  od;

  gens := GeneratorsOfSemigroup(Source(C));
  for m in [2 .. Length(scc)] do
    # Compute homomorphism from G to the corresponding result.groups
    x := hom[scc[m][1]];
    mm := quotient_scc.id[x];
    y := result.reps_pos[mm];
    # Find the path from x to the first component of the scc in the quotient
    # graph (y)
    p := EvaluateWord(gens, DigraphPath(result.graph, x, y)[2]);
    G := LambdaOrbSchutzGp(o, m);
    dom := o[scc[m][1]];
    map := result.rep_homs[mm];
    imgs := List(GeneratorsOfGroup(G),
                  g -> AsPermutation((PartialPerm(dom, OnTuples(dom, g)) ^ (p ^ -1))
                       * result.reps[mm]) ^ map);
    ghom := GroupHomomorphismByImages(G,
                                      Range(map),
                                      GeneratorsOfGroup(G),
                                      imgs);
    result.all_homs[m] := ghom;
  od;

  return result;
end);
