############################################################################
##
##  congruences/cong.gi
##  Copyright (C) 2015-2022                               Michael C. Young
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##
## This file contains some general functions, operations and attributes of
## semigroup congruences.  Methods for specific types of congruence are
## implemented in the following files:
##
##       conginv.gi     - Inverse semigroups
##       congpairs.gi   - Congruences with generating pairs
##       congrees.gi    - Rees congruences
##       congrms.gi     - (0-)simple Rees matrix semigroups
##       congsimple.gi  - (0-)simple semigroups
##       conguniv.gi    - Universal congruences
##
## cong.gd contains declarations for many of these.
##

# Where possible, we only provide methods in this file for
# IsLeftRightOrTwoSidedCongruence and IsLeftRightOrTwoSidedCongruenceClass, and
# not arbitrary congruences.

########################################################################
# 0. Categories
########################################################################

InstallMethod(CongruenceCategory, "for a right congruence category",
[IsRightCongruenceCategory], C -> IsRightCongruenceCategory);

InstallMethod(CongruenceCategory, "for a left congruence category",
[IsLeftCongruenceCategory], C -> IsLeftCongruenceCategory);

InstallMethod(CongruenceCategory, "for a 2-sided congruence category",
[IsCongruenceCategory], C -> IsCongruenceCategory);

InstallMethod(CongruenceCategoryString, "for a right congruence category",
[IsRightCongruenceCategory], C -> "right");

InstallMethod(CongruenceCategoryString, "for a left congruence category",
[IsLeftCongruenceCategory], C -> "left");

InstallMethod(CongruenceCategoryString, "for a 2-sided congruence category",
[IsCongruenceCategory], C -> "2-sided");

########################################################################
# Flexible functions for creating congruences
########################################################################

InstallGlobalFunction(SemigroupCongruence,
function(arg)
  local S, opts, s_opts, x, pairs, cong;
  if not Length(arg) >= 2 then
    ErrorNoReturn("at least 2 arguments are required");
  elif not IsSemigroup(arg[1]) then
    ErrorNoReturn("the 1st argument is not a semigroup");
  fi;
  S := arg[1];

  # Set up any options
  if IsRecord(arg[Length(arg)]) then
    opts := arg[Length(arg)];
    arg := arg{[1 .. Length(arg) - 1]};
  else
    opts := rec();
  fi;
  s_opts := SEMIGROUPS.OptionsRec(S);
  for x in RecNames(s_opts) do
    if not IsBound(opts.(x)) then
      opts.(x) := s_opts.(x);
    fi;
  od;

  if IsHomogeneousList(arg[2]) then
    # We should have a list of generating pairs
    if Length(arg) = 2 then
      pairs := arg[2];
      if not IsEmpty(pairs) and not IsList(pairs[1]) then
        pairs := [pairs];
      fi;
    elif Length(arg) > 2 then
      pairs := arg{[2 .. Length(arg)]};
    fi;
    if not ForAll(pairs, p -> Size(p) = 2) then
      ErrorNoReturn("the 2nd argument (a list of lists) contains lists ",
                    "of size not equal to 2");
    elif not ForAll(pairs, p -> p[1] in S and p[2] in S) then
      ErrorNoReturn("the 2nd argument (a list of lists) contains items ",
                    "that do not belong to the 1st argument (a semigroup)");
    fi;

    # Remove any reflexive pairs
    pairs := Filtered(pairs, p -> p[1] <> p[2]);

    # Decide which representation to use
    if not IsFinite(S)
        or ((HasIsSimpleSemigroup(S) or IsActingSemigroup(S)
           or HasSize(S) or IsReesMatrixSemigroup(S))
          and IsSimpleSemigroup(S)) or
         ((HasIsZeroSimpleSemigroup(S) or IsActingSemigroup(S)
           or HasSize(S) or IsReesZeroMatrixSemigroup(S))
          and IsZeroSimpleSemigroup(S)) then
      return SemigroupCongruenceByGeneratingPairs(S, pairs);
    elif IsInverseSemigroup(S) and IsGeneratorsOfInverseSemigroup(S) and
         Size(S) >= opts.cong_by_ker_trace_threshold then
      cong := SemigroupCongruenceByGeneratingPairs(S, pairs);
      cong := AsInverseSemigroupCongruenceByKernelTrace(cong);
      SetGeneratingPairsOfMagmaCongruence(cong, pairs);
      return cong;
    else
      return SemigroupCongruenceByGeneratingPairs(S, pairs);
    fi;
  elif IsGeneralMapping(arg[2]) and
      ((IsRMSCongruenceByLinkedTriple(arg[3]) and IsSimpleSemigroup(S))
       or (IsRZMSCongruenceByLinkedTriple(arg[3]) and IsZeroSimpleSemigroup(S)))
      then
    # We should have a congruence of an isomorphic RMS/RZMS
    if Range(arg[2]) = Range(arg[3]) and S = Source(arg[2]) then
      return CongruenceByIsomorphism(arg[2], arg[3]);
    else
      ErrorNoReturn("the range of the 3rd argument (a congruence) is ",
                    "not a Rees (0-)matrix semigroup isomorphic to the ",
                    "1st argument");
    fi;
  elif HasIsSemigroupIdeal(arg[2])
      and IsSemigroupIdeal(arg[2])
      and Parent(arg[2]) = S then
    return ReesCongruenceOfSemigroupIdeal(arg[2]);
  elif Length(arg) = 3
      and IsInverseSemigroup(arg[2])
      and IsGeneratorsOfInverseSemigroup(arg[2])
      and IsDenseList(arg[3])
      and IsInverseSemigroup(S)
      and IsGeneratorsOfInverseSemigroup(S) then
    # We should have the kernel and trace of a congruence on an inverse
    # semigroup
    return InverseSemigroupCongruenceByKernelTrace(S, arg[2], arg[3]);
  fi;
  ErrorNoReturn("the arguments are not valid for this function");
end);

BindGlobal("_LeftOrRightCong",
function(CongruenceConstructor, arg)
  local S, pairs;
  if not Length(arg) >= 2 then
    ErrorNoReturn("at least 2 arguments are required");
  elif not IsSemigroup(arg[1]) then
    ErrorNoReturn("the 1st argument is not a semigroup");
  fi;
  S := arg[1];

  if IsHomogeneousList(arg[2]) then
    # We should have a list of generating pairs
    if Length(arg) = 2 then
      pairs := arg[2];
      if not IsEmpty(pairs) and not IsList(pairs[1]) then
        pairs := [pairs];
      fi;
    elif Length(arg) > 2 then
      pairs := arg{[2 .. Length(arg)]};
    fi;
    if not ForAll(pairs, p -> Size(p) = 2) then
      ErrorNoReturn("the 2nd argument (a list of lists) contains lists ",
                    "of size not equal to 2");
    elif not ForAll(pairs, p -> p[1] in S and p[2] in S) then
      ErrorNoReturn("the 2nd argument (a list of lists) contains items ",
                    "that do not belong to the 1st argument (a semigroup)");
    fi;
    # Remove any reflexive pairs
    pairs := Filtered(pairs, p -> p[1] <> p[2]);
    return CongruenceConstructor(S, pairs);
  else
    ErrorNoReturn("the arguments are not valid for this function");
  fi;
end);

InstallGlobalFunction(LeftSemigroupCongruence,
function(arg)
  return _LeftOrRightCong(LeftSemigroupCongruenceByGeneratingPairs, arg);
end);

InstallGlobalFunction(RightSemigroupCongruence,
function(arg)
  return _LeftOrRightCong(RightSemigroupCongruenceByGeneratingPairs, arg);
end);

########################################################################
# Congruence attributes that don't require CanUseFroidurePin
########################################################################

InstallMethod(NonTrivialEquivalenceClasses,
"for a left, right, or 2-sided semigroup congruence",
[IsLeftRightOrTwoSidedCongruence],
function(C)
  local part, nr_classes, classes, i;
  part := EquivalenceRelationPartition(C);
  nr_classes := Length(part);
  classes := EmptyPlist(nr_classes);
  for i in [1 .. nr_classes] do
    classes[i] := EquivalenceClassOfElementNC(C, part[i][1]);
    SetAsList(classes[i], part[i]);
  od;
  return classes;
end);

InstallMethod(EquivalenceRelationCanonicalLookup,
"for a left, right, or 2-sided semigroup congruence",
[IsLeftRightOrTwoSidedCongruence],
function(C)
  local S, lookup;
  S := Range(C);
  if not IsFinite(S) then
    ErrorNoReturn("the argument (a ",
                  CongruenceCategoryString(C),
                  " congruence) must have finite range");
  fi;
  lookup := EquivalenceRelationLookup(C);
  return FlatKernelOfTransformation(Transformation(lookup), Length(lookup));
end);

########################################################################
# Congruence attributes that require CanUseFroidurePin
########################################################################

InstallMethod(EquivalenceRelationLookup,
"for a left, right, or 2-sided semigroup congruence",
[IsLeftRightOrTwoSidedCongruence],
function(C)
  local S, lookup, class, nr, elm;
  S := Range(C);
  if not IsFinite(S) then
    ErrorNoReturn("the argument (a ",
                  CongruenceCategoryString(C),
                  " congruence) must have finite range");
  elif not CanUseFroidurePin(S) then
    # CanUseFroidurePin is required because PositionCanonical is not a thing
    # for other types of semigroups.
    TryNextMethod();
  fi;

  lookup := [1 .. Size(S)];
  for class in EquivalenceRelationPartition(C) do
    nr := PositionCanonical(S, Representative(class));
    for elm in class do
      lookup[PositionCanonical(S, elm)] := nr;
    od;
  od;
  return lookup;
end);

InstallMethod(EquivalenceRelationCanonicalPartition,
"for a left, right, or 2-sided semigroup congruence",
[IsLeftRightOrTwoSidedCongruence],
function(C)
  local S, result, cmp, i;
  S := Range(C);
  if not IsFinite(S) then
    ErrorNoReturn("the argument (a ",
                  CongruenceCategoryString(C),
                  " congruence) must have finite range");
  elif not CanUseFroidurePin(S) then
    # CanUseFroidurePin is required because PositionCanonical is not a thing
    # for other types of semigroups.
    TryNextMethod();
  fi;
  result := ShallowCopy(EquivalenceRelationPartition(C));
  cmp := {x, y} -> PositionCanonical(S, x) < PositionCanonical(S, y);
  for i in [1 .. Length(result)] do
    result[i] := ShallowCopy(result[i]);
    Sort(result[i], cmp);
  od;
  Sort(result, {x, y} -> cmp(Representative(x), Representative(y)));
  return result;
end);

########################################################################
# Congruence operators
########################################################################

InstallMethod(\in,
"for homog. list and IsLeftRightOrTwoSidedCongruence",
[IsHomogeneousList, IsLeftRightOrTwoSidedCongruence],
function(pair, C)
  local S, string;

  if Size(pair) <> 2 then
    ErrorNoReturn("the 1st argument (a list) does not have length 2");
  fi;

  S      := Range(C);
  string := CongruenceCategoryString(C);
  if not (pair[1] in S and pair[2] in S) then
    ErrorNoReturn("the items in the 1st argument (a list) do not all belong to ",
                  "the range of the 2nd argument (a ", string, " semigroup ",
                  "congruence)");
  elif CanEasilyCompareElements(pair[1]) and pair[1] = pair[2] then
    return true;
  fi;
  return CongruenceTestMembershipNC(C, pair[1], pair[2]);
end);

InstallMethod(\=, "for a left, right, or 2-sided semigroup congruence",
[IsLeftRightOrTwoSidedCongruence, IsLeftRightOrTwoSidedCongruence],
function(lhop, rhop)
  local S;
  S := Range(lhop);
  if S <> Range(rhop) then
    return false;
  elif HasIsFinite(S) and IsFinite(S) then
    return EquivalenceRelationCanonicalLookup(lhop) =
           EquivalenceRelationCanonicalLookup(rhop);
  fi;
  return EquivalenceRelationCanonicalPartition(lhop) =
         EquivalenceRelationCanonicalPartition(rhop);
end);

InstallMethod(IsSuperrelation, "for semigroup congruences",
[IsLeftRightOrTwoSidedCongruence, IsLeftRightOrTwoSidedCongruence],
{lhop, rhop} -> IsSubrelation(rhop, lhop));

# TODO what about MeetLeftSemigroupCongruences, MeetRightSemigroupCongruences?
InstallMethod(MeetSemigroupCongruences, "for semigroup congruences",
[IsSemigroupCongruence, IsSemigroupCongruence],
function(lhop, rhop)
  if Range(lhop) <> Range(rhop) then
    Error("cannot form the meet of congruences over different semigroups");
  elif lhop = rhop then
    return lhop;
  elif IsSubrelation(lhop, rhop) then
    return rhop;
  elif IsSubrelation(rhop, lhop) then
    return lhop;
  fi;
  # lhop_lookup := EquivalenceRelationCanonicalLookup(lhop);
  # rhop_lookup := EquivalenceRelationCanonicalLookup(rhop);
  # N           := Length(lhop);

  # hash := HashMap();
  # next := 1;
  # for i in [1 .. N] do
  # The problem is how to represent the meet of the congruences
  # od;
  # TODO actually implement a method
  TryNextMethod();
end);

########################################################################
# Congruence classes
########################################################################

InstallMethod(EquivalenceClassOfElement,
"for a left, right, or 2-sided semigroup congruence and multiplicative element",
[IsLeftRightOrTwoSidedCongruence, IsMultiplicativeElement],
function(C, x)
  if not x in Range(C) then
    ErrorNoReturn("the 2nd argument (a mult. elt.) does not belong ",
                  "to the range of the 1st argument (a ",
                  CongruenceCategoryString(C),
                  " congruence)");
  fi;
  return EquivalenceClassOfElementNC(C, x);
end);

InstallMethod(EquivalenceClassOfElementNC,
"for a left, right, or 2-sided congruence and mult. elt.",
[IsLeftRightOrTwoSidedCongruence, IsMultiplicativeElement],
function(C, x)
  local filt, class;
  if IsCongruenceCategory(C) then
    filt := IsCongruenceClass and IsAttributeStoringRep;
  elif IsLeftCongruenceCategory(C) then
    filt := IsLeftCongruenceClass;
  else
    Assert(1, IsRightCongruenceCategory(C));
    filt := IsRightCongruenceClass;
  fi;

  class := Objectify(NewType(FamilyObj(Range(C)), filt), rec());
  SetParentAttr(class, Range(C));
  SetEquivalenceClassRelation(class, C);
  SetRepresentative(class, x);
  if HasIsFinite(Range(C)) and IsFinite(Range(C)) then
    SetIsFinite(class, true);
  fi;

  return class;
end);

########################################################################
# Congruence class attributes
########################################################################

InstallMethod(AsList,
"for a class of a left, right, or 2-sided semigroup congruence",
[IsLeftRightOrTwoSidedCongruenceClass],
C -> ImagesElm(EquivalenceClassRelation(C), Representative(C)));

InstallMethod(Enumerator,
"for a class of a left, right, or 2-sided semigroup congruence",
[IsLeftRightOrTwoSidedCongruenceClass],
6,  # To beat the library method for magma congruence classes
AsList);

InstallMethod(Size,
"for a class of a left, right, or 2-sided semigroup congruence",
[IsLeftRightOrTwoSidedCongruenceClass],
C -> Size(AsList(C)));

########################################################################
# Congruence class operators
########################################################################

# Multiplication for congruence classes: only makes sense for 2-sided
InstallMethod(\*, "for two congruence classes",
[IsCongruenceClass, IsCongruenceClass],
function(lhop, rhop)
  if EquivalenceClassRelation(lhop) <> EquivalenceClassRelation(rhop) then
    ErrorNoReturn("the arguments (cong. classes) are not classes of the same ",
                  "congruence");
  fi;
  return EquivalenceClassOfElementNC(EquivalenceClassRelation(lhop),
                                     Representative(lhop) *
                                     Representative(rhop));
end);

InstallMethod(\=,
"for classes of a left, right, or 2-sided semigroup congruence",
IsIdenticalObj,
[IsLeftRightOrTwoSidedCongruenceClass, IsLeftRightOrTwoSidedCongruenceClass],
function(lhop, rhop)
  return EquivalenceClassRelation(lhop) = EquivalenceClassRelation(rhop)
    and [Representative(lhop), Representative(rhop)]
    in EquivalenceClassRelation(lhop);
end);

InstallMethod(\in,
"for a mult. elt. and a class of a left, right or 2-sided congruence",
[IsMultiplicativeElement, IsLeftRightOrTwoSidedCongruenceClass],
function(x, class)
  local C;
  C := EquivalenceClassRelation(class);
  return x in Range(C) and [x, Representative(class)] in C;
end);

InstallMethod(ViewObj, "for a left, right, or 2-sided semigroup congruence",
[IsLeftRightOrTwoSidedCongruenceClass],
function(C)
  local string;
  string := CongruenceCategoryString(EquivalenceClassRelation(C));
  Print("<", string, " congruence class of ");
  ViewObj(Representative(C));
  Print(">");
end);

########################################################################
# Congruence class actions
########################################################################

InstallMethod(OnLeftCongruenceClasses,
"for a left congruence class and a multiplicative element",
[IsLeftCongruenceClass, IsMultiplicativeElement],
function(class, x)
  local C;
  C := EquivalenceClassRelation(class);
  return EquivalenceClassOfElementNC(C, x * Representative(class));
end);

InstallMethod(OnRightCongruenceClasses,
"for a right congruence class and a multiplicative element",
[IsRightCongruenceClass, IsMultiplicativeElement],
function(class, x)
  local C;
  C := EquivalenceClassRelation(class);
  return EquivalenceClassOfElementNC(C, Representative(class) * x);
end);
