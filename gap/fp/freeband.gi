###############################################################################
##
##  freeband.gi
##  Copyright (C) 2013-15                                  Julius Jonusas
##
##  Licensing information can be foundin the README file of this package.
##
###############################################################################

# TODO: this is not really finished.

# TODO
# InstallMethod(FreeBandOfFreeBandElement,

InstallMethod(ContentOfFreeBandElement, "for a free band element",
[IsFreeBandElement],
function(w)
  return ListBlist([1 .. Length(w!.cont)], w!.cont);
end);

InstallMethod(ContentOfFreeBandElementCollection,
"for a free band element collection",
[IsFreeBandElementCollection],
function(coll)
  local n, content, w;

  n := Length(coll[1]!.cont);
  content := BlistList([1 .. n], []);

  for w in coll do
    UniteBlist(content, w!.cont);
    if SizeBlist(content) = n then
      break;
    fi;
  od;

  return ListBlist([1 .. n], content);
end);

###############################################################################
## Internal
###############################################################################

SEMIGROUPS.FreeBandElmToWord := function(elem)
  local tuple, out, first, pre_tuple, last, su_tuple, word1, word2;

  tuple := elem!.tuple;

  if elem!.word <> fail then
    return elem!.word;
  elif tuple![2] = 0 then  # tuple corresponds to one the generators
    out := [tuple![1]];
  else
    first := tuple![1];
    pre_tuple := tuple![2];  # tuple correspoding to the prefix
    last := tuple![3];
    su_tuple := tuple![4];  # tuple corresponding to the sufix

    # if first = last we only need a single letter
    if first = last then
      out := Concatenation(SEMIGROUPS.FreeBandElmToWord(pre_tuple), [first],
                           SEMIGROUPS.FreeBandElmToWord(su_tuple));
      # otherwise we need distinct letters for both first and last
    else
      word1 := Concatenation(SEMIGROUPS.FreeBandElmToWord(pre_tuple), [first]);
      word2 := Concatenation([last], SEMIGROUPS.FreeBandElmToWord(su_tuple));
      if word1 = word2 then
        out := word1;
      else
        out := Concatenation(word1, word2);
      fi;
    fi;
  fi;
  elem!.word := out;
  return out;
end;

SEMIGROUPS.HashFunctionForFreeBandElements := function(x, data)
  return ORB_HashFunctionForPlainFlatList(SEMIGROUPS.FreeBandElmToWord(x),
                                          data);
end;

InstallMethod(IsGeneratorsOfInverseSemigroup, "for a free band element coll",
[IsFreeBandElementCollection], ReturnFalse);

InstallTrueMethod(IsFinite, IsFreeBandSubsemigroup);

InstallGlobalFunction(FreeBand,
function(arg)
  local names, F, type, ngens, gens, filts, S, m;

  # Get and check the argument list, and construct names if necessary.
  if Length(arg) = 1 and IsInt(arg[1]) and 0 < arg[1] then
    names := List([1 .. arg[1]],
                  i -> Concatenation("x", String(i)));
  elif Length(arg) = 2 and IsInt(arg[1]) and 0 < arg[1]
      and IsString(arg[2]) then
    names := List([1 .. arg[1]],
                  i -> Concatenation(arg[2], String(i)));
  elif 1 <= Length(arg) and ForAll(arg, IsString) then
    names := arg;
  elif Length(arg) = 1 and IsList(arg[1])
      and ForAll(arg[1], IsString) then
    names := arg[1];
  else
    ErrorNoReturn("FreeBand(<name1>,<name2>..) or FreeBand(<rank> [, name])");
  fi;

  MakeImmutable(names);

  F := NewFamily("FreeBandElementsFamily", IsFreeBandElement,
                                           CanEasilySortElements);

  type := NewType(F, IsFreeBandElement and IsPositionalObjectRep);

  ngens := Length(names);
  gens := EmptyPlist(ngens);

  for m in [1 .. ngens] do
    gens[m] := Objectify(type, rec(tuple := [m, 0, m, 0],
                                   cont := BlistList([1 .. ngens], [m]),
                                   word := [m]));
  od;

  StoreInfoFreeMagma(F, names, IsFreeBandElement);

  filts := IsFreeBandCategory and IsAttributeStoringRep and IsWholeFamily and
           IsFreeBand;

  S := Objectify(NewType(FamilyObj(gens), filts),
                 rec(opts := SEMIGROUPS.DefaultOptionsRec));

  SetGeneratorsOfMagma(S, gens);

  FamilyObj(S)!.semigroup := S;
  F!.semigroup := S;

  return S;
end);

InstallMethod(IsFreeBand, "for a semigroup",
[IsSemigroup],
function(S)
  local used, occurred, gens, max_d, g;

  if not IsBand(S) then
    return false;
  fi;

  if IsFreeBandSubsemigroup(S) then
    gens := Generators(S);
    used := BlistList([1 .. Length(gens[1]!.cont)], []);
    occurred := BlistList([1 .. Length(gens[1]!.cont)], []);
    for g in gens do
      used := IntersectionBlist(used, g!.cont);
      if g!.tuple[2] = 0 then
        occurred[g!.tuple[1]] := true;
      fi;
    od;
    if used = occurred then
      return true;
    fi;
  fi;

  if not IsActingSemigroup(S) then
    S := AsSemigroup(IsTransformationSemigroup, S);
  fi;

  max_d := MaximalDClasses(S);
  return Size(S) = Size(FreeBand(Length(max_d)));
end);

InstallMethod(Iterator, "for a Greens D-class of a free band",
[IsFreeBandElementCollection and IsGreensDClass],
function(dclass)
  local NextIterator_FreeBandDClass, NewIterator_FreeBandDClass,
  ShallowCopyLocal, record, s, content, rep,
  NextIterator_FreeBandDClassWithPrint;

  s := Parent(dclass);
  rep := Representative(dclass);
  content := rep!.cont;

  NextIterator_FreeBandDClass := function(iter)
    local output, i, content, tempcont, tuple;

    if iter!.element <> fail then
      # output := StructuralCopy(iter!.element); doesn't work
      output := rec(tuple := StructuralCopy(iter!.element!.tuple),
                    content := ShallowCopy(iter!.element!.content),
                    word := ShallowCopy(iter!.element!.word));
    else
      return fail;
    fi;

    content := iter!.content;
    tuple := iter!.element!.tuple;
    iter!.element!.word := fail;

    if tuple[2] = 0 then
      iter!.element := fail;
    elif iter!.iter1!.element <> fail then
      # Prefix word is not done yet
      tuple[2] := NextIterator_FreeBandDClass(iter!.iter1);
      iter!.element!.tuple := tuple;
    elif Position(content, true, tuple[1]) <> fail then
      # Update the first component
      i := Position(content, true, tuple[1]);
      tuple[1] := i;
      tempcont := ShallowCopy(content);
      tempcont[i] := false;
      iter!.iter1 := NewIterator_FreeBandDClass(iter!.semigroup, tempcont);
      tuple[2] := NextIterator_FreeBandDClass(iter!.iter1);
      iter!.element!.tuple := tuple;
    elif iter!.iter2!.element <> fail then
      # Suffix word is not done yet
      tuple[4] := NextIterator_FreeBandDClass(iter!.iter2);
      iter!.element!.tuple := tuple;
      # Restart the prefix
      i := Position(content, true);
      tuple[1] := i;
      tempcont := ShallowCopy(content);
      tempcont[i] := false;
      iter!.iter1 := NewIterator_FreeBandDClass(iter!.semigroup, tempcont);
      tuple[2] := NextIterator_FreeBandDClass(iter!.iter1);
      iter!.element!.tuple := tuple;
    elif Position(content, true, tuple[3]) <> fail then
      # Update the third component
      i := Position(content, true, tuple[3]);
      tuple[3] := i;
      tempcont := ShallowCopy(content);
      tempcont[i] := false;
      iter!.iter2 := NewIterator_FreeBandDClass(iter!.semigroup, tempcont);
      tuple[4] := NextIterator_FreeBandDClass(iter!.iter2);
      # Restart the prefix
      i := Position(content, true);
      tuple[1] := i;
      tempcont := ShallowCopy(content);
      tempcont[i] := false;
      iter!.iter1 := NewIterator_FreeBandDClass(iter!.semigroup, tempcont);
      tuple[2] := NextIterator_FreeBandDClass(iter!.iter1);
      iter!.element!.tuple := tuple;
    else
      iter!.element := fail;
    fi;
    return output;
  end;

  #

  NextIterator_FreeBandDClassWithPrint := function(iter)
    local next_value;

    next_value := NextIterator_FreeBandDClass(iter);

    if next_value = fail then
      return fail;
    else
      return Product(List(SEMIGROUPS.FreeBandElmToWord(next_value),
                     x -> GeneratorsOfSemigroup(iter!.semigroup)[x]));
    fi;
  end;

  #

  NewIterator_FreeBandDClass := function(s, content)
    local record, first, tempcont, elem;

    first := Position(content, true);
    elem := Objectify(TypeObj(s.1), rec(tuple := [],
                                        content := content,
                                        word := fail));

    # If the content is of size one
    if Position(content, true, first) = fail then
      elem!.tuple := [first, 0, first, 0];
      elem!.word := [first];
      record := rec(element := elem,
                    iter1 := fail,
                    iter2 := fail,
                    semigroup := s,
                    content := content) ;
    else
      tempcont := ShallowCopy(content);
      tempcont[first] := false;
      record := rec(element := elem,
                    iter1 := NewIterator_FreeBandDClass(s, tempcont),
                    iter2 := NewIterator_FreeBandDClass(s, tempcont),
                    semigroup := s,
                    content := content);
      record!.element!.tuple := [first,
                                 NextIterator_FreeBandDClass(record!.iter1),
                                 first,
                                 NextIterator_FreeBandDClass(record!.iter2)];
    fi;
    return record;
  end;

  #

  ShallowCopyLocal := record ->
    rec(last_called_by_is_done := record!.last_called_by_is_done,
        next_value := record!.next_value,
        IsDoneIterator := record!.IsDoneIterator,
        NextIterator := record!.NextIterator);

  record := NewIterator_FreeBandDClass(s, content);
  record!.NextIterator := NextIterator_FreeBandDClassWithPrint;
  record!.ShallowCopy := ShallowCopyLocal;
  return IteratorByNextIterator(record);
end);

InstallMethod(GreensDClassOfElement, "for a free band and element",
[IsFreeBandCategory, IsFreeBandElement],
function(S, x)
  local filt, type, D;
  if not x in S then
    ErrorNoReturn("the 2nd argument (a free band element) does not ",
                  "belong to 1st argument (a free band category)");
  fi;

  filt := IsEquivalenceClass and IsEquivalenceClassDefaultRep
          and IsGreensDClass;

  if Length(GeneratorsOfSemigroup(S)) < 4 then
    filt := filt and IsGreensClassOfSemigroupThatCanComputeFroidurePinRep;
  fi;

  type := NewType(FamilyObj(S), filt);
  D := Objectify(type, rec());
  SetParent(D, S);
  SetRepresentative(D, x);
  SetEquivalenceClassRelation(D, GreensDRelation(S));

  return D;
end);

InstallMethod(ViewString, "for a free band element",
[IsFreeBandElement], PrintString);

InstallMethod(PrintString, "for a free band element",
[IsFreeBandElement],
function(elem)
  return Concatenation(List(SEMIGROUPS.FreeBandElmToWord(elem),
                            x -> FamilyObj(elem)!.names[x]));
end);

InstallMethod(ViewObj, "for a free band",
[IsFreeBandCategory],
function(S)
  if GAPInfo.ViewLength * 10 < Length(GeneratorsOfMagma(S)) then
    Print("<free band with ", Length(GeneratorsOfSemigroup(S)),
          " generators>");
  else
    Print("<free band on the generators ",
          GeneratorsOfSemigroup(S), ">");
  fi;
end);

InstallMethod(EqualInFreeBand, "for two strings",
[IsString, IsString],
function(w1_in, w2_in)
  if IsEmpty(w1_in) or IsEmpty(w2_in) then
    return IsEmpty(w1_in) and IsEmpty(w2_in);
    # Necessary since [] is recognised as a string yet the below
    # doesn't work with it.
  fi;
  w1_in := List(w1_in, IntChar);
  w2_in := List(w2_in, IntChar);
  return EqualInFreeBand(w1_in, w2_in);
end);

# This is an implementation of the algorithm described in Jakub Radoszewski
# and Wojciech Rytter's paper 'Efficient Testing of Equivalence of Words
# in a Free Idempotent Semigroup⋆'

InstallMethod(EqualInFreeBand, "for two lists of positive integers",
[IsHomogeneousList, IsHomogeneousList],
function(w1_in, w2_in)
  local Right, Left, LevelEdges, RadixSort, StripFreeBandString, w1, w2, dollar,
  l1, l2, w, c, check, rightk, leftk, edgecodes, rightm, leftm, i, k;

  Right := function(w, k)
    local right, i, j, content_size, multiplicity, length_w;

    length_w := Length(w);
    if length_w = 0 then
      return [];
    fi;

    j            := 0;
    right        := [];
    content_size := 0;
    multiplicity := ListWithIdenticalEntries(Maximum(w), 0);

    for i in [1 .. length_w] do
      if i > 1 then
        multiplicity[w[i - 1]] := multiplicity[w[i - 1]] - 1;
        if multiplicity[w[i - 1]] = 0 then
          content_size := content_size - 1;
        fi;
      fi;
      while j < length_w and
          (multiplicity[w[j + 1]] <> 0 or content_size < k) do
        j := j + 1;
        if multiplicity[w[j]] = 0 then
          content_size := content_size + 1;
        fi;
        multiplicity[w[j]] := multiplicity[w[j]] + 1;
      od;
      if content_size = k then
        right[i] := j;
      else
        right[i] := fail;
      fi;
    od;
    return right;
  end;

  Left := function(w, k)
    local i, left, length_w;

    length_w := Length(w);
    w        := StandardiseWord(Reversed(w));
    left     := Reversed(Right(w, k));
    for i in [1 .. length_w] do
      if left[i] <> fail then
        left[i] := length_w - left[i] + 1;
      fi;
    od;
    return left;
  end;

  LevelEdges := function(w, k, radix, rightk, leftk, rightm, leftm)
    local n, outr, outl, i;

    n    := Length(w);
    outr := [];
    outl := [];

    if k = 1 then
      for i in [1 .. n] do
        Add(outr, [1, w[i], w[i], 1]);
        Add(outl, [1, w[i], w[i], 1]);
      od;
    else
      for i in [1 .. n] do
        if rightk[i] <> fail then
          Add(outr, [radix[i], w[rightm[i] + 1],
                     w[leftm[rightk[i]] - 1], radix[rightk[i] + n]]);
        else
          Add(outr, [fail, fail, fail, fail]);
        fi;

        if leftk[i] <> fail then
          Add(outl, [radix[leftk[i]], w[rightm[leftk[i]] + 1],
                     w[leftm[i] - 1], radix[i + n]]);
        else
          Add(outl, [fail, fail, fail, fail]);
        fi;
      od;
    fi;
    return Concatenation(outr, outl);
  end;

  RadixSort := function(level_edges, alphabet_size)
    local B, result, count_sort, i, n, counter;

    count_sort := function(B, i, radix)
      local counts, j, result;

      counts := ListWithIdenticalEntries(radix + 1, 0);
      for j in [1 .. Length(B)] do
        if level_edges[B[j]][i] <> fail then
          counts[level_edges[B[j]][i]] := counts[level_edges[B[j]][i]] + 1;
        else
          counts[radix + 1] := counts[radix + 1] + 1;
        fi;
      od;
      for j in [2 .. radix + 1] do
        counts[j] := counts[j] + counts[j - 1];
      od;
      result := [1 .. Length(B)];
      for j in [Length(B), Length(B) - 1 .. 1] do
        if level_edges[B[j]][i] <> fail then
          result[counts[level_edges[B[j]][i]]] := B[j];
          counts[level_edges[B[j]][i]]         :=
                                      counts[level_edges[B[j]][i]] - 1;
        else
          result[counts[radix + 1]] := B[j];
          counts[radix + 1]         := counts[radix + 1] - 1;
        fi;
      od;
      return result;
    end;

    n := Length(level_edges);
    B := [1 .. n];
    B := count_sort(B, 1, n);
    B := count_sort(B, 2, alphabet_size);
    B := count_sort(B, 3, alphabet_size);
    B := count_sort(B, 4, n);

    result  := ListWithIdenticalEntries(n, fail);
    counter := 1;
    for i in [2 .. n] do
      if level_edges[B[i]] <> level_edges[B[i - 1]] then
        counter := counter + 1;
      fi;
      result[B[i]] := counter;
    od;
    result[B[1]] := 1;

    return result;
  end;

  StripFreeBandString := function(w)
    local last, out, i;
    if not IsList(w) then
      ErrorNoReturn("expected a list, got ", w);
    fi;
    if Length(w) = 0 or Length(w) = 1 then
      return w;
    fi;

    last := w[1];
    out  := [last];
    for i in [2 .. Length(w)] do
      if w[i] <> last then
        Add(out, w[i]);
        last := w[i];
      fi;
    od;
    return out;
  end;

  if IsEmpty(w1_in) or IsEmpty(w2_in) then
    return IsEmpty(w1_in) and IsEmpty(w2_in);
  fi;

  w1 := StripFreeBandString(w1_in);
  w2 := StripFreeBandString(w2_in);

  if w1 = w2 then
    return true;
  fi;

  dollar := Maximum(Maximum(w1), Maximum(w2)) + 1;
  l1     := Length(w1);
  l2     := Length(w2);

  w := Concatenation(w1, [dollar], w2);
  w := StandardiseWord(w);

  c     := w[l1 + 1];
  check := ListWithIdenticalEntries(c, false);
  for i in [l1 + 2 .. l1 + 1 + l2] do
    if w[i] >= c then
      return false;
    else
      check[w[i]] := true;
    fi;
  od;
  if SizeBlist(check) <> c - 1 then
    return false;
  fi;

  if c = 2 then
    return true;
  fi;

  rightk    := [];
  leftk     := [];
  edgecodes := [];

  for k in [1 .. c - 1] do
    rightm := rightk;
    leftm  := leftk;

    rightk := Right(w, k);
    leftk  := Left(w, k);

    edgecodes := LevelEdges(w, k, edgecodes, rightk, leftk, rightm, leftm);

    edgecodes := RadixSort(edgecodes, c);
  od;

  return edgecodes[1] = edgecodes[l1 + 2];
end);

# TODO Is there a more efficient way to compare elements? JJ

InstallMethod(\=, "for elements of a free band",
IsIdenticalObj, [IsFreeBandElement, IsFreeBandElement],
function(x, y)
  local i;

  if x!.cont <> y!.cont then
    return false;
  fi;
  for i in [1 .. 4] do
    if x!.tuple![i] <> y!.tuple![i] then
      return false;
    fi;
  od;
  return true;
end);

# TODO Is it possible to find a non recursive way to compare elements? JJ

InstallMethod(\<, "for elements of a free band",
IsIdenticalObj, [IsFreeBandElement, IsFreeBandElement],
function(x, y)
  local i, tuple1, tuple2;

  tuple1 := x!.tuple;
  tuple2 := y!.tuple;

  i := 1;
  while i <= 3 and tuple1![i] = tuple2![i] do
    i := i + 1;
  od;

  if tuple2[i] = 0  then
    return false;
  elif tuple1[i] = 0 then
    return true;
  fi;
  return tuple1[i] < tuple2[i];
end);

InstallMethod(\*, "for elements of a free band", IsIdenticalObj,
[IsFreeBandElement, IsFreeBandElement],
function(x, y)
  local type, out, diff, new_first, new_prefix, new_last, new_sufix, copy;

  type := TypeObj(x);
  # if the content of two elements is the same we only need the prefix of the
  # first and the sufix of the second one
  # cont = blist
  if IsSubsetBlist(x!.cont, y!.cont) then
    out := [x!.tuple[1], x!.tuple[2]];
  else
    diff := DifferenceBlist(y!.cont, x!.cont);
    # new_first is the last letter to occur first in the product
    new_first := y!.tuple[1];
    new_prefix := y!.tuple[2];
    while true do
      if diff[new_first] and new_prefix = 0 then
        copy := ShallowCopy(x);  # are shallow copies necessary?
        out := [new_first, copy];
        break;
      elif diff[new_first] then
        copy := ShallowCopy(x * new_prefix);
        out := [new_first, copy];
        break;
      else
        new_first := new_prefix!.tuple[1];
        new_prefix := new_prefix!.tuple[2];
      fi;
    od;
  fi;

  if IsSubsetBlist(y!.cont, x!.cont) then
    out{[3, 4]} := [y!.tuple[3], y!.tuple[4]];
  else
    diff := DifferenceBlist(x!.cont, y!.cont);
    # new_last is the first letter to occur for the last time in the product
    new_last := x!.tuple[3];
    new_sufix := x!.tuple[4];
    repeat
      if diff[new_last] and new_sufix = 0 then
        copy := ShallowCopy(y);
        out{[3 .. 4]} := [new_last, copy];
        break;
      elif diff[new_last] then
        copy := ShallowCopy(new_sufix * y);
        out{[3, 4]} := [new_last, copy];
        break;
      else
        new_last := new_sufix!.tuple[3];
        new_sufix := new_sufix!.tuple[4];
      fi;
    until IsBound(out[3]);
  fi;

  return Objectify(type, rec(tuple := out,
                             cont := UnionBlist(x!.cont, y!.cont),
                             word := fail));
end);

InstallMethod(Size, "for a free band",
[IsFreeBandCategory and IsFinite and HasGeneratorsOfSemigroup],
function(S)
  local c, output, k, i, n;

  n := Length(FamilyObj(S.1)!.names);

  c := [];
  for k in [1 .. n] do
    c[k] := 1;
    for i in [1 .. k - 1] do
      c[k] := c[k] * (k - i + 1) ^ (2 ^ i);
    od;
  od;

  output := 0;
  for k in [1 .. n] do
    output := output + Binomial(n, k) * c[k];
  od;

  return output;
end);

InstallMethod(ChooseHashFunction, "for a free band element and int",
[IsFreeBandElement, IsInt],
function(x, hashlen)
  return rec(func := SEMIGROUPS.HashFunctionForFreeBandElements,
             data := hashlen);
end);
