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

InstallImmediateMethod(CanUseLibsemigroupsCongruence,
                       IsInverseSemigroupCongruenceByKernelTrace,
                       0,
                       ReturnFalse);

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
    ErrorNoReturn("the 3rd argument must be a 2-sided congruence of the",
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
  local S, o, i, j, m, aa, rep, l, e, g, im_g, K, T, Pi, Pj, lookup, result, G, N, x, h;

  S := Range(C);
  if not a in S then
    ErrorNoReturn("the 2nd argument (a mult. elt. with inverse) does not ",
                  "belong to the range of the 1st argument (a congruence)");
  fi;

  K := KernelOfSemigroupCongruence(C);
  T := TraceOfSemigroupCongruence(C);

  o  := LambdaOrb(S);
  i  := Position(o, LambdaFunc(S)(a));
  j  := Position(o, RhoFunc(S)(a));
  m  := OrbSCCLookup(o)[i];
  aa := LambdaOrbMult(o, m, j)[1] * a * LambdaOrbMult(o, m, i)[2];

  rep := LambdaOrbRep(o, m);
  l   := Position(o, RhoFunc(S)(rep));
  rep := LambdaOrbMult(LambdaOrb(S), m, l)[1] * rep;

  e := MeetOfPartialPerms(ImagesElm(T, PartialPerm(o[i], o[i])));
  g := LambdaPerm(S)(rep, aa);
  Error();
  im_g := RightCoset(SchutzenbergerGroup(HClass(K, e)), g) ;


  Pi := EquivalenceClassOfElementNC(T, PartialPerm(o[i], o[i]));
  Pi := List(Pi, x -> Position(o, ImageSetOfPartialPerm(x)));

  Pj := EquivalenceClassOfElementNC(T, PartialPerm(o[j], o[j]));
  Pj := List(Pj, x -> Position(o, ImageSetOfPartialPerm(x)));
  # TODO isn't Pi = Pj always?
  lookup := OrbSCCLookup(o);

  result := [];

  for i in Pi do
    for j in Pj do
      if lookup[i] = lookup[j] then
        m := lookup[i];
        rep := LambdaOrbRep(o, m);
        N := SchutzenbergerGroup(HClassNC(K, rep));
        Error();
        x := LambdaPerm(S)(rep, rep * g);
        for h in RightCoset(N, x) do
          Add(result, LambdaOrbMult(o, m, j)[2] * rep * h * LambdaOrbMult(o, m, i)[1]);
        od;
      fi;
    od;
  od;
  return result;
end);

# TODO replace

InstallMethod(EquivalenceRelationPartitionWithSingletons,
"for inverse semigroup congruence by kernel and trace",
[IsInverseSemigroupCongruenceByKernelTrace],
function(C)
  local S, elmlists, kernel, trace, blockelmlists, pos, traceBlock, id, elm;

  S := Range(C);
  elmlists := [];
  kernel := KernelOfSemigroupCongruence(C);
  trace := TraceOfSemigroupCongruence(C);

  # Consider each trace-class in turn
  for traceBlock in EquivalenceRelationPartitionWithSingletons(trace) do
    # Consider all the congruence classes corresponding to this trace-class
    blockelmlists := [];   # List of lists of elms in class
    for id in traceBlock do
      for elm in LClassNC(S, id) do
        # Find the congruence class that this element lies in
        pos := PositionProperty(blockelmlists,
                                class -> elm * class[1] ^ -1 in kernel);
        if pos = fail then
          # New class
          Add(blockelmlists, [elm]);
        else
          # Add to the old class
          Add(blockelmlists[pos], elm);
        fi;
      od;
    od;
    Append(elmlists, blockelmlists);
  od;
  return elmlists;
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
  local S, T, trace, pairs, result;

  S := Source(C);
  if not (IsInverseSemigroup(S) and IsGeneratorsOfInverseSemigroup(S)) then
    ErrorNoReturn("the range of the argument (a congruence) must be an ",
                  "inverse semigroup with inverse op");
  fi;
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

SEMIGROUPS.KernelTraceClosure := function(S, kernel, trace, genpairs)
  local kernel_gens_to_add, trace_pairs_to_add, x, enumerate_trace, pair,
  enforce_conditions, y;

  # This function takes an inverse semigroup S, a subsemigroup ker, an
  # equivalence traceBlocks on the idempotents, and a list of pairs in S.
  # It returns the minimal congruence containing "kernel" in its kernel and
  # "trace" in its trace, and containing all the given pairs

  kernel := InverseSubsemigroup(S, kernel);
  Enumerate(kernel);
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
