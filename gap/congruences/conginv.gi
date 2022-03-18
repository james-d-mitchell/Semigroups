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

TracePicture := function(C)
  local S, D, reps, trace, part, lookup, colors, i, j;

  S := IdempotentGeneratedSubsemigroup(Source(C));
  D := PartialOrderOfDClasses(S);
  reps := DClassReps(S);
  trace := TraceOfSemigroupCongruence(C);
  part := List(EquivalenceRelationPartitionWithSingletons(trace), ShallowCopy);
  for i in [1 .. Length(part)] do
    for j in [1 .. Length(part[i])] do
      part[i][j] := Position(reps, part[i][j]);
    od;
  od;
  lookup := [];
  colors := DIGRAPHS_GraphvizColors();
  for i in [1 .. Length(part)] do
    lookup{part[i]} := ListWithIdenticalEntries(Length(part[i]), colors[i * 5]);
  od;
  return [D, lookup];
end;

CheckHypothesis := function(C)
  local S, K, result, seen, HK, DS, pos, HS, DK;

  S := Source(C);
  K := KernelOfSemigroupCongruence(C);
  result := NrEquivalenceClasses(TraceOfSemigroupCongruence(C));
  seen := BlistList([1 .. NrDClasses(S)], []);

  for DK in DClasses(K) do
    HK := GroupHClass(DK);
    DS := DClass(S, MultiplicativeNeutralElement(HK));
    pos := Position(DClasses(S), DS);
    if not seen[pos] then 
      seen[pos] := true;
      Print(pos, ": ", (Size(DS) / Size(DK)) - (NrRClasses(DS) / NrRClasses(DK)), "\n");
      result := result + (Size(DS) / Size(DK)) - (NrRClasses(DS) / NrRClasses(DK));
    fi;
  od;
  return result;
end;

PartitionDClass := function(C, D)
  return Filtered(List(EquivalenceRelationPartitionWithSingletons(C), x -> Filtered(x, y -> y in D)), x -> not IsEmpty(x));
end;

CheckHypothesis2 := function(C)
  local i, part, sizes, D;
  
  i := 0;
  for D in DClasses(Source(C)) do
    i := i + 1;
    part := List(EquivalenceRelationPartitionWithSingletons(C), x -> Filtered(x, y -> y in D));
    sizes := ShallowCopy(AsSSortedList(List(part, Size)));
    RemoveSet(sizes, 0);
    if Size(sizes) > 1 then
      Print(C, D, part, "\n");
      return false;
    fi;
    Print(i, " : ", sizes[1], "\n");
  od;
  return true;
end;

if IsPackageMarkedForLoading("io", "4.4.4") then

  __JDMS_GLOBAL_TIMINGS_RECORD := rec(running := false);

  StartTimer := function()
    if not __JDMS_GLOBAL_TIMINGS_RECORD.running then
      __JDMS_GLOBAL_TIMINGS_RECORD.timeofday := IO_gettimeofday();
    fi;
  end;

  # Time in microseconds!
  ElapsedTimer := function()
    local  timeofday, elapsed;
    if IsBound(__JDMS_GLOBAL_TIMINGS_RECORD) and
        IsBound(__JDMS_GLOBAL_TIMINGS_RECORD.timeofday) then

      timeofday := IO_gettimeofday();
      elapsed := (timeofday.tv_sec - __JDMS_GLOBAL_TIMINGS_RECORD.timeofday.tv_sec)
                  * 10 ^ 6 + Int((timeofday.tv_usec -
                   __JDMS_GLOBAL_TIMINGS_RECORD.timeofday.tv_usec));
      return elapsed;
    else
      return 0;
    fi;
  end;

  StopTimer := function()
    local t;
    t := ElapsedTimer();
    __JDMS_GLOBAL_TIMINGS_RECORD.running := false;
    Unbind(__JDMS_GLOBAL_TIMINGS_RECORD.timeofday);
    return t;
  end;

  Benchmark := function(func, arg)
    local t;
    StartTimer();
    CallFuncList(func, arg);
    t := StopTimer();
    GASMAN("collect");
    return t;
  end;
fi;

InstallGlobalFunction(InverseSemigroupCongruenceByKernelTrace,
function(S, kernel, traceBlocks)
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
  for traceClass in traceBlocks do
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
  # TODO(later) check trace is *normal*
  return InverseSemigroupCongruenceByKernelTraceNC(S, kernel, traceBlocks);
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
  return(Range(lhop) = Range(rhop) and
         lhop!.kernel = rhop!.kernel and
         lhop!.traceBlocks = rhop!.traceBlocks);
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
  return IsSubsemigroup(lhop!.kernel, rhop!.kernel)
         and ForAll(rhop!.traceBlocks,
                    b2 -> ForAny(lhop!.traceBlocks, b1 -> IsSubset(b1, b2)));
end);

InstallMethod(ImagesElm,
"for inverse semigroup congruence by kernel and trace and mult. elt.",
[IsInverseSemigroupCongruenceByKernelTrace,
 IsMultiplicativeElementWithInverse],
function(C, elm)
  local S, images, e, b;
  S := Range(C);
  if not elm in S then
    ErrorNoReturn("the 2nd argument (a mult. elt. with inverse) does not ",
                  "belong to the range of the 1st argument (a congruence)");
  fi;
  images := [];
  # Consider all idempotents trace-related to (a^-1 a)
  for e in First(TraceOfSemigroupCongruence(C), c -> (elm ^ -1 * elm) in c) do
    for b in LClass(S, e) do
      if elm * b ^ -1 in KernelOfSemigroupCongruence(C) then
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
  local S, elmlists, kernel, blockelmlists, pos, traceBlock, id, elm;

  S := Range(C);
  elmlists := [];
  kernel := KernelOfSemigroupCongruence(C);

  # Consider each trace-class in turn
  for traceBlock in
    EquivalenceRelationPartitionWithSingletons(TraceOfSemigroupCongruence(C))
    do
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

InstallMethod(CongruenceTestMembershipNC,
"for inverse semigroup congruence by kernel and trace and two mult. elts",
[IsInverseSemigroupCongruenceByKernelTrace,
 IsMultiplicativeElement,
 IsMultiplicativeElement],
function(C, x, y)
  # Is (a^-1 a, b^-1 b) in the trace?
  if x ^ -1 * x in
      First(TraceOfSemigroupCongruence(C), c -> y ^ -1 * y in c) then
    # Is ab^-1 in the kernel?
    if x * y ^ -1 in KernelOfSemigroupCongruence(C) then
      return true;
    fi;
  fi;
  return false;
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
  local S, invcong, copy;
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
  local S, invcong, copy;
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
  local S;
  S := Range(C);
  if not (IsInverseSemigroup(S) and IsGeneratorsOfInverseSemigroup(S)) then
    ErrorNoReturn("the range of the argument (a congruence) must be an ",
                  "inverse semigroup with inverse op");
  fi;
  return
    SEMIGROUPS.KernelTraceClosureNew(S,
                                  IdempotentGeneratedSubsemigroup(S),
                                  # List(Idempotents(S), e -> [e]),
 SemigroupCongruenceByGeneratingPairs(IdempotentGeneratedSubsemigroup(S), []),
                                  GeneratingPairsOfSemigroupCongruence(C));
end);

InstallMethod(JoinSemigroupCongruences,
"for inverse semigroup congruence",
[IsInverseSemigroupCongruenceByKernelTrace,
 IsInverseSemigroupCongruenceByKernelTrace],
function(lhop, rhop)
  local S, gens1, gens2, kernel, traceBlocks, block, b1, j, pos;
  S := Range(lhop);
  if S <> Range(rhop) then
    Error("cannot form the join of congruences over different semigroups");
  fi;

  # kernel generated by union of lhop's kernel and rhop's kernel
  gens1 := GeneratorsOfInverseSemigroup(lhop!.kernel);
  gens2 := GeneratorsOfInverseSemigroup(rhop!.kernel);
  kernel := InverseSemigroup(Concatenation(gens1, gens2));

  # trace is join of lhop's trace and rhop's trace
  traceBlocks := StructuralCopy(lhop!.traceBlocks);
  for block in rhop!.traceBlocks do
    b1 := PositionProperty(traceBlocks, b -> block[1] in b);
    for j in [2 .. Size(block)] do
      if not block[j] in traceBlocks[b1] then
        # Combine the classes
        pos := PositionProperty(traceBlocks, b -> block[j] in b);
        Append(traceBlocks[b1], traceBlocks[pos]);
        Unbind(traceBlocks[pos]);
      fi;
    od;
    traceBlocks := Compacted(traceBlocks);
  od;

  # Take the kernel-trace closure to ensure we have a correct congruence
  return SEMIGROUPS.KernelTraceClosure(S, kernel, traceBlocks, []);
end);

InstallMethod(MeetSemigroupCongruences,
"for two inverse semigroup congruence",
[IsInverseSemigroupCongruenceByKernelTrace,
 IsInverseSemigroupCongruenceByKernelTrace],
function(lhop, rhop)
  local S, kernel, traceBlocks, ids, c2lookup, classnos, block, classno;
  S := Range(lhop);
  if S <> Range(rhop) then
    Error("cannot form the meet of congruences over different semigroups");
  fi;

  # Calculate the intersection of the kernels
  # TODO(later): can we do this without enumerating the whole kernel?
  kernel := InverseSemigroup(Intersection(lhop!.kernel, rhop!.kernel));
  kernel := InverseSemigroup(SmallInverseSemigroupGeneratingSet(kernel));

  # Calculate the intersection of the traces
  traceBlocks := [];
  ids := IdempotentGeneratedSubsemigroup(S);
  c2lookup := rhop!.traceLookup;
  for block in lhop!.traceBlocks do
    classnos := c2lookup{List(block, x -> Position(ids, x))};
    for classno in DuplicateFreeList(classnos) do
      Add(traceBlocks, block{Positions(classnos, classno)});
    od;
  od;

  return InverseSemigroupCongruenceByKernelTrace(S, kernel, traceBlocks);
end);

SEMIGROUPS.KernelTraceClosure := function(S, kernel, traceBlocks, pairstoapply)
  local canonical_lookup, idsmgp, idslist, slist, kernelgenstoapply, gen, nrk,
        nr, traceUF, i, pos1, j, pos, hashlen, ht, right, genstoapply,
        NormalClosureInverseSemigroup, enumerate_trace, enforce_conditions,
        compute_kernel, oldLookup, oldKernel, trace_unchanged, kernel_unchanged;

  # This function takes an inverse semigroup S, a subsemigroup ker, an
  # equivalence traceBlocks on the idempotents, and a list of pairs in S.
  # It returns the minimal congruence containing "kernel" in its kernel and
  # "traceBlocks" in its trace, and containing all the given pairs
  # TODO(later) Review this JDM for use of Elements, AsList etc. Could
  # iterators work better?

  canonical_lookup := function(uf)
    local N;
    N := SizeUnderlyingSetDS(traceUF);
    return FlatKernelOfTransformation(Transformation([1 .. N],
                                                     x -> Representative(uf, x)),
                                      N);
  end;

  idsmgp  := IdempotentGeneratedSubsemigroup(S);
  idslist := AsListCanonical(idsmgp);
  slist   := AsListCanonical(S);

  # Retrieve the initial information
  kernel := InverseSubsemigroup(S, kernel);
  kernelgenstoapply := Set(pairstoapply, x -> x[1] * x[2] ^ -1);
  # kernel might not be normal, so make sure to check its generators too
  for gen in GeneratorsOfInverseSemigroup(kernel) do
    AddSet(kernelgenstoapply, gen);
  od;
  nrk := Length(kernelgenstoapply);
  Enumerate(kernel);
  pairstoapply := List(pairstoapply,
                       x -> [PositionCanonical(idsmgp, RightOne(x[1])),
                             PositionCanonical(idsmgp, RightOne(x[2]))]);
  nr := Length(pairstoapply);

  # Calculate traceUF from traceBlocks
  traceUF := PartitionDS(IsPartitionDS, Length(idslist));
  for i in [1 .. Length(traceBlocks)] do
    pos1 := PositionCanonical(idsmgp, traceBlocks[i][1]);
    for j in [2 .. Length(traceBlocks[i])] do
      Unite(traceUF, pos1, PositionCanonical(idsmgp, traceBlocks[i][j]));
    od;
  od;

  # Setup some useful information
  pos := 0;
  hashlen := SEMIGROUPS.OptionsRec(S).hashlen;
  ht := HTCreate([1, 1], rec(forflatplainlists := true,
                             treehashsize := hashlen));
  right := OutNeighbours(RightCayleyDigraph(idsmgp));
  genstoapply := [1 .. Length(right[1])];

  #
  # The functions that do the work:
  #
  NormalClosureInverseSemigroup := function(S, K, coll)
    local T, opts, x, list;
    # This takes an inv smgp S, an inv subsemigroup K, and some elms coll,
    # then creates the *normal closure* of K with coll inside S.
    # It assumes K is already normal.
    T := ClosureInverseSemigroup(K, coll);
    while K <> T do
      K := T;
      opts := rec();
      opts.gradingfunc := function(o, x)
        return x in K;
      end;
      opts.onlygrades := function(x, data)
        return x = false;
      end;
      opts.onlygradesdata := fail;
      for x in K do
        list := Enumerate(Orb(GeneratorsOfSemigroup(S), x, OnPoints, opts));
        list := AsList(list);
        T := ClosureInverseSemigroup(T, list);
      od;
    od;
    return K;
  end;

  enumerate_trace := function()
    local a, j, x, y, z;
    if pos = 0 then
      # Add the generating pairs themselves
      for x in pairstoapply do
        if x[1] <> x[2] and HTValue(ht, x) = fail then
          HTAdd(ht, x, true);
          Unite(traceUF, x[1], x[2]);
          # Add each pair's "conjugate" pairs
          for a in GeneratorsOfSemigroup(S) do
            z := [PositionCanonical(idsmgp, a ^ -1 * idslist[x[1]] * a),
                  PositionCanonical(idsmgp, a ^ -1 * idslist[x[2]] * a)];
            if z[1] <> z[2] and HTValue(ht, z) = fail then
              HTAdd(ht, z, true);
              nr := nr + 1;
              pairstoapply[nr] := z;
              Unite(traceUF, z[1], z[2]);
            fi;
          od;
        fi;
      od;
    fi;

    while pos < nr do
      pos := pos + 1;
      x := pairstoapply[pos];
      for j in genstoapply do
        # Add the pair's right-multiples (idsmgp is commutative)
        y := [right[x[1]][j], right[x[2]][j]];
        if y[1] <> y[2] and HTValue(ht, y) = fail then
          HTAdd(ht, y, true);
          nr := nr + 1;
          pairstoapply[nr] := y;
          Unite(traceUF, y[1], y[2]);
          # Add the pair's "conjugate" pairs
          for a in GeneratorsOfSemigroup(S) do
            z := [PositionCanonical(idsmgp, a ^ -1 * idslist[x[1]] * a),
                  PositionCanonical(idsmgp, a ^ -1 * idslist[x[2]] * a)];
            if z[1] <> z[2] and HTValue(ht, z) = fail then
              HTAdd(ht, z, true);
              nr := nr + 1;
              pairstoapply[nr] := z;
              Unite(traceUF, z[1], z[2]);
            fi;
          od;
        fi;
      od;
    od;
  end;

  enforce_conditions := function()
    local traceTable, traceBlocks, a, e, f, classno, blocks, bl, N;
    blocks := PartsOfPartitionDS(traceUF);
    traceBlocks := [];
    for bl in blocks do
      traceBlocks[Representative(traceUF, bl[1])] := bl;
    od;
    N := SizeUnderlyingSetDS(traceUF);
    traceTable := List([1 .. N], x -> Representative(traceUF, x));
    for a in slist do
      if a in kernel then
        e := PositionCanonical(idsmgp, LeftOne(a));
        f := PositionCanonical(idsmgp, RightOne(a));
        if traceTable[e] <> traceTable[f] then
          nr := nr + 1;
          pairstoapply[nr] := [e, f];
        fi;
      else
        classno := traceTable[PositionCanonical(idsmgp, RightOne(a))];
        for e in traceBlocks[classno] do
          if a * idslist[e] in kernel then
            nrk := nrk + 1;
            AddSet(kernelgenstoapply, a);
            break;
            # JDM is this correct? Why repeatedly add the same a to
            # kernelgenstoapply?
          fi;
        od;
      fi;
    od;
  end;

  compute_kernel := function()
    # Take the normal closure inverse semigroup containing the new elements
    if kernelgenstoapply <> [] then
      kernel := NormalClosureInverseSemigroup(S, kernel,
                                              kernelgenstoapply);
      Enumerate(kernel);
      kernelgenstoapply := [];
      nrk := 0;
    fi;
  end;

  # Keep applying the method until no new info is found
  repeat
    oldLookup := canonical_lookup(traceUF);
    oldKernel := kernel;
    compute_kernel();
    enforce_conditions();
    enumerate_trace();
    trace_unchanged := (oldLookup = canonical_lookup(traceUF));
    kernel_unchanged := (oldKernel = kernel);
    Info(InfoSemigroups, 3, "lookup: ", trace_unchanged);
    Info(InfoSemigroups, 3, "kernel: ", kernel_unchanged);
    Info(InfoSemigroups, 3, "nrk = 0: ", nrk = 0);
  until trace_unchanged and kernel_unchanged and (nrk = 0);

  # Convert traceLookup to traceBlocks
  traceBlocks := List(Compacted(PartsOfPartitionDS(traceUF)),
                      b -> List(b, i -> idslist[i]));

  return InverseSemigroupCongruenceByKernelTraceNC(S, kernel, traceBlocks);
end;

########################################################################

SEMIGROUPS.KernelTraceClosureNew := function(S, kernel, trace, pairs)
  local kernelgenstoapply, tracepairs, NormalClosureInverseSemigroup,
  enumerate_trace, enforce_conditions, compute_kernel;

  kernel := InverseSubsemigroup(S, kernel);
  Enumerate(kernel);
  kernelgenstoapply := Set(pairs, x -> x[1] * x[2] ^ -1);
  # kernel might not be normal, so make sure to check its generators too
  UniteSet(kernelgenstoapply, GeneratorsOfInverseSemigroup(kernel));
  tracepairs := Set(pairs, x -> Set([RightOne(x[1]), RightOne(x[2])]));

  NormalClosureInverseSemigroup := function(S, K, coll)
    local T, opts, x, list;
    # This takes an inv smgp S, an inv subsemigroup K, and some elms coll,
    # then creates the *normal closure* of K with coll inside S.
    # It assumes K is already normal.
    T := ClosureInverseSemigroup(K, coll);

    while K <> T do
      K := T;
      opts := rec();
      opts.gradingfunc := function(o, x)
        return x in T;
      end;
      opts.onlygrades := function(x, data)
        return x = false;
      end;
      opts.onlygradesdata := fail;
      for x in GeneratorsOfSemigroup(K) do
        list := AsList(Enumerate(Orb(GeneratorsOfSemigroup(S), x, POW, opts)));
        T := ClosureInverseSemigroup(T, list);
      od;
    od;
    return K;
  end;

  enforce_conditions := function()
    local e, f, enum, D, i, j, a;
    Print(ListWithIdenticalEntries(72, '#'), "\n");
    Print("#I  enforce_conditions()\n");

    StartTimer();
    # C2 condition
    for D in DClasses(kernel) do
      for i in [1 .. NrIdempotents(D) - 1] do
        e := Idempotents(D)[i];
        for j in [i + 1 .. NrIdempotents(D)] do
          f := Idempotents(D)[j];
          if not CongruenceTestMembershipNC(trace, e, f) then
            Add(tracepairs, Set([e, f]));
          fi;
        od;
      od;
    od;
    if not IsEmpty(tracepairs) then
      Print("#I  elapsed time: ", StopTimer(), " microseconds\n");
      return;
    fi;

    enum := EnumeratorCanonical(kernel);
    for a in EnumeratorCanonical(S) do
      if not a in enum then
        f := RightOne(a);
        for e in ImagesElm(trace, f) do
          # C1 condition
          if a * e in enum then
            AddSet(kernelgenstoapply, a);
            break;
          fi;
        od;
      fi;
    od;
    Print("#I  elapsed time: ", StopTimer(), " microseconds\n");
  end;

  compute_kernel := function()
    Print(ListWithIdenticalEntries(72, '#'), "\n");
    Print("#I  compute_kernel(", Size(kernelgenstoapply), " generators)\n");
    StartTimer();
    if not IsEmpty(kernelgenstoapply) then
      kernel := NormalClosureInverseSemigroup(S,
                                              kernel,
                                              kernelgenstoapply);
      Enumerate(kernel);
      kernelgenstoapply := [];
    fi;
    Print("#I  elapsed time: ", StopTimer(), " microseconds\n");
  end;

  enumerate_trace := function()
    local opts, act, pairs, x, pair;

    Print(ListWithIdenticalEntries(72, '#'), "\n");
    Print("#I  enumerate_trace(", Size(tracepairs), " pairs)\n");
    StartTimer();

    tracepairs := Filtered(Set(tracepairs), x -> Size(x) = 2);
    for pair in tracepairs do
      if not CongruenceTestMembershipNC(trace, pair[1], pair[2]) then
        pairs := ShallowCopy(GeneratingPairsOfSemigroupCongruence(trace));
        Add(pairs, pair);
        trace := SemigroupCongruenceByGeneratingPairs(Source(trace), pairs);
      fi;
    od;
    tracepairs := [];
    Print("#I  elapsed time: ", StopTimer(), " microseconds\n");
  end;

  compute_kernel();
  enforce_conditions();

  # Keep applying the method until no new info is found
  while not IsEmpty(kernelgenstoapply) or not IsEmpty(tracepairs) do
    #Info(InfoSemigroups, 3, "kernel size: ", Size(kernel));
    #Info(InfoSemigroups, 3, "number of trace classes: ", NrEquivalenceClasses(trace));
    #Info(InfoSemigroups, 3, "number of kernel generators: ", Size(kernelgenstoapply));
    #Info(InfoSemigroups, 3, "number of trace pairs: ", Size(tracepairs));
    Print(ListWithIdenticalEntries(72, '#'), "\n");
    enumerate_trace();
    compute_kernel();
    enforce_conditions();
  od;
  return InverseSemigroupCongruenceByKernelTraceNC(S, kernel, trace);
end;

InstallMethod(MinimumGroupCongruence,
"for an inverse semigroup with inverse op",
[IsInverseSemigroup and IsGeneratorsOfInverseSemigroup],
# This is the maximum congruence whose quotient is a group
function(S)
  local ker, leq, n, x, traceBlocks;

  # Kernel should be the majorant closure of the idempotents
  ker := IdempotentGeneratedSubsemigroup(S);
  leq := NaturalLeqInverseSemigroup(S);
  for n in ker do
    for x in S do
      if leq(n, x) and not x in ker then
        ker := ClosureInverseSemigroup(ker, x);
      fi;
    od;
  od;
  ker := InverseSemigroup(SmallInverseSemigroupGeneratingSet(ker));

  # Trace should be the universal congruence
  traceBlocks := [Idempotents(S)];

  return InverseSemigroupCongruenceByKernelTraceNC(S, ker, traceBlocks);
end);
