#############################################################################
##
#W  greenstar.gd
#Y  Copyright (C) 2017                  James D. Mitchell & Simon Tollman
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

InstallMethod(ViewObj, "for a Green's *-relation",
[IsGreensStarRelation],
AbsInt(RankFilter(IsLeftSemigroupCongruence)
- RankFilter(IsGreensStarRelation)) + 1,
function(rel)
  Print(ViewString(rel));
end);

InstallMethod(ViewString, "for a Green's *-relation",
[IsGreensStarRelation],
AbsInt(RankFilter(IsLeftSemigroupCongruence)
- RankFilter(IsGreensStarRelation)) + 1,
function(rel)
  local  str;
  str := "\><";
  Append( str, "\>Green's\< " );
  if IsGreensDStarRelation(rel)  then
    Append( str, "D" );
  elif IsGreensRStarRelation(rel)  then
    Append(str, "R");
  elif IsGreensLStarRelation(rel)  then
    Append(str, "L");
  elif IsGreensHStarRelation(rel)  then
    Append( str, "H" );
  fi;
  Append(str, "*-relation of ");
  Append(str, ViewString(Source(rel)));
  Append(str, ">\<" );
  return str;
end);

InstallMethod(ViewObj, "for a Green's *-class",
[IsGreensStarClass],
function(C)
  Print(ViewString(C));
end);

InstallMethod(ViewString, "for a Green's *-class",
[IsGreensStarClass],
function(C)
  local str;
  str := "\><";
  Append( str, "\>Green's\< " );
  if IsGreensDStarClass(C) then
    Append(str, "D");
  elif IsGreensRStarClass(C) then
    Append(str, "R");
  elif IsGreensLStarClass(C) then
    Append(str, "L");
  elif IsGreensHStarClass(C) then
    Append(str, "H");
  fi;
  Append(str, "*-class: ");
  Append(str, ViewString(Representative(C)));
  Append(str, ">\<");
  return str;
end);

InstallMethod(GreensRStarRelation, "for a semigroup", [IsSemigroup],
function(S)
  local fam, type, rel;

  fam := GeneralMappingsFamily(ElementsFamily(FamilyObj(S)),
                               ElementsFamily(FamilyObj(S)));

  type := NewType(fam,
                  IsEquivalenceRelation
                  and IsEquivalenceRelationDefaultRep
                  and IsGreensRStarRelation);

  rel := Objectify(type, rec());

  SetSource(rel, S);
  SetRange(rel, S);

  SetIsLeftSemigroupCongruence(rel, true);
  return rel;
end);

InstallMethod(GreensRStarClassType, "for a semigroup",
[IsSemigroup],
function(S)
  return NewType(FamilyObj(S), IsEquivalenceClassDefaultRep
                               and IsGreensRStarClass);
end);

InstallMethod(EquivalenceClassOfElement, 
"for a Green's *-relation and multiplicative element",
[IsGreensStarRelation, IsMultiplicativeElement], 
function(rel, x)
  local out, type;

  if not x in Source(rel) then 
    ErrorNoReturn("TODO");
  fi;

  out := rec();
  if IsGreensRStarRelation(rel) then 
    type := GreensRStarClassType(Source(rel));
  else
    ErrorNoReturn("TODO");
  fi;

  ObjectifyWithAttributes(out, type, 
                          EquivalenceClassRelation, rel,
                          Representative, x, 
                          ParentAttr, Source(rel));
  return out;
end);

InstallMethod(GreensRStarClass, 
"for a semigroup and a multiplicative element", 
[IsSemigroup, IsMultiplicativeElement], 
function(S, x)
  return EquivalenceClassOfElement(GreensRStarRelation(S), x);
end);
