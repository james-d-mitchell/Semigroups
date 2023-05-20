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

InstallImmediateMethod(CanUseLibsemigroupsCongruence,
                       IsInverseSemigroupCongruenceByKernelTrace,
                       0,
                       ReturnFalse);

InstallGlobalFunction(InverseSemigroupCongruenceByKernelTrace,
function(S, kernel, trace)
  local a, x, traceClass, f, l, e;
  if not IsInverseSemigroup(S)
      and IsMultiplicativeElementWithInverseCollection(S) then
    ErrorNoReturn("the 1st argument is not an inverse ",
                  "semigroup with inverse op");
  elif not IsInverseSubsemigroup(S, kernel) then
    # Check that the kernel is an inverse subsemigroup
    ErrorNoReturn("the 2nd argument is not an inverse ",
                  "subsemigroup of the 1st argument (an inverse semigroup)");
    # CHECK KERNEL IS NORMAL:
  elif NrIdempotents(kernel) <> NrIdempotents(S) then
    # (1) Must contain all the idempotents of S
    ErrorNoReturn("the 2nd argument (an inverse semigroup) does not contain ",
                  "all of the idempotents of the 1st argument (an inverse",
                  " semigroup)");
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

  # (2) Must be self-conjugate
  for a in kernel do
    for x in GeneratorsOfSemigroup(S) do
      if not a ^ x in kernel then
        ErrorNoReturn("the 2nd argument (an inverse semigroup) must be ",
                      "self-conjugate");
      fi;
    od;
  od;
  # Check conditions for a congruence pair: Howie p.156
  for traceClass in EquivalenceClasses(trace) do
    for f in traceClass do
      l := LClass(S, f);
      for a in l do
        if a in kernel then
          # Condition (C2): aa' related to a'a
          if not a * a ^ -1 in traceClass then
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
  Print("<semigroup congruence over ");
  ViewObj(Range(C));
  Print(" with congruence pair (",
        Size(KernelOfSemigroupCongruence(C)), ",",
        NrEquivalenceClasses(TraceOfSemigroupCongruence(C)), ")>");
end);

InstallMethod(\=,
"for two inverse semigroup congruences by kernel and trace",
[IsInverseSemigroupCongruenceByKernelTrace,
 IsInverseSemigroupCongruenceByKernelTrace],
function(lhop, rhop)
  return(Range(lhop) = Range(rhop)
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
  local S, images, trace, e, b;

  S := Range(C);
  if not a in S then
    ErrorNoReturn("the 2nd argument (a mult. elt. with inverse) does not ",
                  "belong to the range of the 1st argument (a congruence)");
  fi;
  images := [];
  # Consider all idempotents trace-related to (a^-1 a)
  trace := TraceOfSemigroupCongruence(C);
  for e in EquivalenceClassOfElementNC(trace, a ^ -1 * a) do
    for b in LClass(S, e) do
      if a * b ^ -1 in KernelOfSemigroupCongruence(C) then
        Add(images, b);
      fi;
    od;
  od;
  return images;
end);

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
      for elm in LClass(S, id) do
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

# The next method is slower than using the standard non-inverse semigroup
# methods
# InstallMethod(NrEquivalenceClasses,
# "for inverse semigroup congruence by kernel and trace",
# [IsInverseSemigroupCongruenceByKernelTrace],
# function(C)
#   local S, kernel, trace, blockelmlists, pos, count, block, e, a;
# 
#   if HasEquivalenceRelationPartitionWithSingletons(C) then
#     return Size(EquivalenceRelationPartitionWithSingletons(C));
#   fi;
# 
#   S := Range(C);
#   kernel := KernelOfSemigroupCongruence(C);
#   trace := TraceOfSemigroupCongruence(C);
#   count := 0;
# 
#   # Consider each trace-class in turn
#   for block in EquivalenceRelationPartitionWithSingletons(trace) do
#     # Consider all the congruence classes corresponding to this trace-class
#     blockelmlists := [];   # List of lists of elms in class
#     for e in block do
#       for a in LClass(S, e) do
#         # Find the congruence class that this element lies in
#         pos := PositionProperty(blockelmlists,
#                                 class -> a * class[1] ^ -1 in kernel);
#         if pos = fail then
#           # New class
#           Add(blockelmlists, [a]);
#         else
#           # Add to the old class
#           Add(blockelmlists[pos], a);
#         fi;
#       od;
#     od;
#     count := count + Size(blockelmlists);
#   od;
#   return count;
# end);

InstallMethod(CongruenceTestMembershipNC,
"for inverse semigroup congruence by kernel and trace and two mult. elts",
[IsInverseSemigroupCongruenceByKernelTrace,
 IsMultiplicativeElement,
 IsMultiplicativeElement],
function(C, x, y)
  return CongruenceTestMembershipNC(TraceOfSemigroupCongruence(C),
                                    x * x ^ -1,
                                    y * y ^ -1)
         and x * y ^ -1 in KernelOfSemigroupCongruence(C);
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
[IsSemigroupCongruence and HasGeneratingPairsOfMagmaCongruence],
function(C)
  local S, T, trace;

  S := Source(C);
  if not (IsInverseSemigroup(S) and IsGeneratorsOfInverseSemigroup(S)) then
    ErrorNoReturn("the range of the argument (a congruence) must be an ",
                  "inverse semigroup with inverse op");
  fi;
  T := IdempotentGeneratedSubsemigroup(S);
  trace := SemigroupCongruenceByGeneratingPairs(T, []);
  return SEMIGROUPS.KernelTraceClosure(S,
                                       T,
                                       trace,
                                       GeneratingPairsOfSemigroupCongruence(C));
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
                             GeneratorsOfInverseSemigroup(rker));

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
  local kernel_gens_to_add, trace_pairs_to_add,
  NormalClosureInverseSemigroup, x, enumerate_trace, pair,
  enforce_conditions, compute_kernel;

  # This function takes an inverse semigroup S, a subsemigroup ker, an
  # equivalence traceBlocks on the idempotents, and a list of pairs in S.
  # It returns the minimal congruence containing "kernel" in its kernel and
  # "trace" in its trace, and containing all the given pairs

  kernel := InverseSubsemigroup(S, kernel);
  Enumerate(kernel);
  kernel_gens_to_add := Set(genpairs, x -> x[1] * x[2] ^ -1);
  UniteSet(kernel_gens_to_add, GeneratorsOfInverseSemigroup(kernel));

  trace_pairs_to_add := List(genpairs, x -> [RightOne(x[1]), RightOne(x[2])]);
  AsListCanonical(S);  # makes the computation below somewhat faster

  NormalClosureInverseSemigroup := function(S, K, coll)
    local T, opts, x, list;
    # This takes an inv smgp S, an inv subsemigroup K, and some elms coll,
    # then creates the *normal closure* of K with coll inside S.
    # It assumes K is already normal.
    T := ClosureInverseSemigroup(K, coll);

    opts := rec();
    opts.onlygrades := function(x, data)
      return x = false;
    end;
    opts.onlygradesdata := fail;

    while K <> T do
      K := T;
      opts.gradingfunc := function(o, x)
        return x in T;
      end;
      for x in GeneratorsOfSemigroup(K) do
        list := AsList(Enumerate(Orb(GeneratorsOfSemigroup(S), x, POW, opts)));
        T := ClosureInverseSemigroup(T, list);
      od;
    od;
    return K;
  end;

  enumerate_trace := function()
    local pairs, pair, a;
    for pair in Set(trace_pairs_to_add) do
      if not CongruenceTestMembershipNC(trace, pair[1], pair[2]) then
        pairs := ShallowCopy(GeneratingPairsOfSemigroupCongruence(trace));
        Add(pairs, pair);
        trace := SemigroupCongruenceByGeneratingPairs(Source(trace), pairs);
      fi;
      for a in GeneratorsOfSemigroup(S) do
        if not CongruenceTestMembershipNC(trace,
                                          a ^ -1 * pair[1] * a,
                                          a ^ -1 * pair[2] * a) then
          pairs := ShallowCopy(GeneratingPairsOfSemigroupCongruence(trace));
          Add(pairs, [a ^ -1 * pair[1] * a, a ^ -1 * pair[2] * a]);
          trace := SemigroupCongruenceByGeneratingPairs(Source(trace), pairs);
        fi;
      od;
    od;
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
         f := RightOne(a);
         for e in ImagesElm(trace, f) do
           # C1 condition
           if a * e in enum then
             AddSet(kernel_gens_to_add, a);
             break;
           fi;
         od;
       fi;
     od;
   end;

  compute_kernel := function()
    # Take the normal closure inverse semigroup containing the new elements
    if kernel_gens_to_add <> [] then
      kernel := NormalClosureInverseSemigroup(S,
                                              kernel,
                                              kernel_gens_to_add);
      Enumerate(kernel);
      kernel_gens_to_add := [];
    fi;
  end;

  repeat
    enumerate_trace();
    compute_kernel();
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

# TODO(later) this is a completely generic version implementation, surely we
# can do better than this!

InstallMethod(GeneratingPairsOfMagmaCongruence,
"for inverse semigroup congruence by kernel and trace",
[IsInverseSemigroupCongruenceByKernelTrace],
function(C)
  local CC, pairs, class, i, j;

  pairs := [];
  CC := SemigroupCongruenceByGeneratingPairs(Source(C), pairs);
  for class in EquivalenceRelationPartition(C) do
    for i in [2 .. Length(class)] do
      if not CongruenceTestMembershipNC(CC, class[i], class[1]) then
        pairs := GeneratingPairsOfSemigroupCongruence(CC);
        pairs := Concatenation(pairs, [[class[i], class[1]]]);
        CC := SemigroupCongruenceByGeneratingPairs(Source(C), pairs);
        # TODO break when CC = C
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

  if not IsInverseSemigroup(Source(C)) or not IsSubsemigroup(S, Source(C)) then
    ErrorNoReturn();
  fi;

  A := GeneratorsOfSemigroup(S);
  P := GeneratingPairsOfSemigroupCongruence(C);
  for p in P do
    for a in A do
      if not CongruenceTestMembershipNC(C,
                                        a ^ -1 * p[1] * a,
                                        a ^ -1 * p[2] * a) then
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
  T := IdempotentGeneratedSubsemigroup(S);
  princ := PrincipalCongruencesOfSemigroup(S, Combinations(AsList(T), 2));
  return List(princ, TraceOfSemigroupCongruence);
end);

InstallMethod(NormalCongruencesIdempotentSemilattice,
"for an inverse semigroup", [IsInverseSemigroup],
function(S)
  local princ;
  princ := ShallowCopy(PrincipalNormalCongruencesIdempotentSemilattice(S));
  Add(princ, TrivialCongruence(IdempotentGeneratedSubsemigroup(S)));
  return CongruencesOfPoset(JoinSemilatticeOfCongruences(princ));
end);
