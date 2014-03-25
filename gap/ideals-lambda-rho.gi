############################################################################
##
#W  ideals-lambda-rho.gi
#Y  Copyright (C) 2013-14                                James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

InstallMethod(Enumerate, "for an ideal orb, and a number", 
[IsIdealOrb, IsCyclotomic], 
function(o, limit)
  local newlookfunc;

  newlookfunc := function(data, x)
    return IsClosed(o) or Length(o) >= limit;
  end;
  Enumerate(SemigroupData(o!.parent), infinity, newlookfunc);

  return o;
end);

# JDM: this doesn't make any sense, the argument <lookfunc> should be applied to
# the elements of <o> not the points in <data!.orbit>, which is what is
# happening here...

InstallMethod(Enumerate, "for an ideal orb, a number, and a function", 
[IsIdealOrb, IsCyclotomic, IsFunction], 
function(o, limit, lookfunc)
  local newlookfunc;
  
  newlookfunc := function(data, x)
    return IsClosed(o) or Length(o) >= limit
           or lookfunc(o, x);
  end;
  Enumerate(SemigroupData(o!.parent), infinity, newlookfunc);

  return o;
end);

#

InstallMethod(Length, "for a ideal orb", 
[IsIdealOrb],
function(o)
  return Sum(o!.lens);
end);

#

InstallMethod(IsBound\[\], "for an ideal orb and positive integer",
[IsIdealOrb, IsPosInt], 
function(o, i)
  local nr;

  nr:=1;
  while IsBound(o!.orbits[nr]) and i>Length(o!.orbits[nr]) do 
    i:=i-Length(o!.orbits[nr]);
    nr:=nr+1;
  od;
  return IsBound(o!.orbits[nr]) and IsBound(o!.orbits[nr][i]);
end);

#

InstallMethod(ELM_LIST, "for an ideal orb and positive integer",
[IsIdealOrb, IsPosInt], 
function(o, i)
  local nr;

  nr:=1;
  while i>Length(o!.orbits[nr]) do 
    i:=i-Length(o!.orbits[nr]);
    nr:=nr+1;
  od;
  return o!.orbits[nr][i];
end);

#

InstallMethod(\in, "for an object and ideal orb",
[IsObject, IsIdealOrb],
function(obj, o)
  return HTValue(o!.ht, obj)<>fail;
end);

#

InstallMethod(Position, "for an ideal orb, object, zero cyc",
[IsIdealOrb, IsObject, IsZeroCyc],
function(o, obj, n)
  return HTValue(o!.ht, obj);
end);

#

InstallMethod(OrbitGraph, "for an ideal orb",
[IsIdealOrb],
function(o)
  return o!.orbitgraph;
end);

#

InstallMethod(ViewObj, "for a ideal orb", 
[IsIdealOrb],
function(o)
  Print("<");
  if IsClosed(o) then 
    Print("closed ");
  else
    Print("open ");
  fi;
  Print("ideal ");
  if IsIdealLambdaOrb(o) then 
    Print("lambda ");
  else
    Print("rho ");
  fi;
  
  Print("orbit with ", Length(o)-1, " points in ", Length(o!.orbits)-1, 
  " components>");
  return;
end);

# different method for inverse semigroup ideals

InstallMethod(LambdaOrb, "for an acting semigroup ideal", 
[IsActingSemigroup and IsSemigroupIdeal],
function(I)
  local record, htopts, fam;
  
  record:=rec();
  record.orbits:=[[fail]];      record.lens:=[1];    
  record.parent:=I;             record.scc:=[[1]];       
  record.scc_reps:=[fail,];     record.scc_lookup:=[1];
  record.schreiergen:=[fail];   record.schreierpos:=[fail];
  record.orbitgraph:=[[]];      
  record.gens:=GeneratorsOfSemigroup(SupersemigroupOfIdeal(I));
  record.orbschreierpos := [];
  record.orbschreiergen := [];
  record.orbschreiercmp := []; 
  # data!.orbits[i] is obtained from data!.orbits[data!.orbschreiercmp[i]] by
  # applying some generator
  record.orbtogen := [];
  
  htopts:=ShallowCopy(LambdaOrbOpts(I)); 
  htopts.treehashsize:=I!.opts.hashlen.M;
  record.ht:=HTCreate(LambdaFunc(I)(Representative(I)), htopts);
  
  fam:=CollectionsFamily(FamilyObj(LambdaFunc(I)(Representative(I))));
  return Objectify(NewType(fam, IsIdealLambdaOrb), record);
end);

# this is essentially the same as the method for a semigroup defined by a
# generating set...

InstallMethod(LambdaOrb, "for an inverse op acting semigroup ideal", 
[IsActingSemigroupWithInverseOp and IsSemigroupIdeal],
function(I)
  local record, gens, lambdafunc, o, ht, nr, nrgens, lambda, InstallPointInOrb,
   x, i;

  record:=ShallowCopy(LambdaOrbOpts(I));
  record.scc_reps:=[FakeOne(GeneratorsOfSemigroupIdeal(I))];
  
  record.schreier:=true;        record.orbitgraph:=true;
  record.storenumbers:=true;    record.log:=true;
  record.parent:=I;             record.treehashsize:=I!.opts.hashlen.M;
  record.orbtogen:=[]; # orbtogen[Position(o, LambdaFunc(I)(gens[i]))]=i

  gens:=GeneratorsOfSemigroupIdeal(I);
  lambdafunc:=LambdaFunc(I);
  
  o:=Orb(GeneratorsOfSemigroup(SupersemigroupOfIdeal(I)), LambdaOrbSeed(I),
   LambdaAct(I), record);
 
  # install the lambda values of the generators
  ht:=o!.ht;  nr:=1;  nrgens:=Length(gens);
  lambdafunc:=LambdaFunc(I);
  
  #
  InstallPointInOrb:=function(lambda)
    nr:=nr+1;
    HTAdd(ht, lambda, nr);
    Add(o!.orbit, lambda);
    Add(o!.schreierpos, fail);
    Add(o!.schreiergen, fail);
    Add(o!.orbitgraph, []);
  end;
  #
  
  for i in [1..nrgens] do 
    x:=gens[i]; 
    lambda:=lambdafunc(x);
    if HTValue(ht, lambda)=fail then 
      InstallPointInOrb(lambda);
      o!.orbtogen[nr]:=i;
    fi;
    
    lambda:=lambdafunc(x^-1);
    if HTValue(ht, lambda)=fail then 
      InstallPointInOrb(lambda);
      o!.orbtogen[nr]:=nrgens+i;
    fi;
  od;
  o!.pos:=2; #don't apply the generators of the supersemigroup of <I> to the
             #dummy point at the start of the orbit (otherwise we just get the
             #lambda orbit of the supersemigroup

  SetFilterObj(o, IsLambdaOrb and IsInverseIdealOrb); 
  return o;
end);

# assumes that <pt> is not in <o> already...

InstallGlobalFunction(UpdateIdealLambdaOrb, 
function(o, pt, x, pos, gen, ind)
  local I, record, len, new, ht, nrorb, cmp, i;

  I:=o!.parent; 
  record:=ShallowCopy(LambdaOrbOpts(I));
  
  record.schreier:=true;        record.orbitgraph:=true;
  record.storenumbers:=true;    record.log:=true;
  record.parent:=I;             record.treehashsize:=I!.opts.hashlen.M;
 
  len:=Length(o);

  if len<>0 then 
    record.gradingfunc:=function(new, x)
      return x in o;
    end;
    record.onlygrades:=function(x, data);
      return not x;
    end;
    record.onlygradesdata:=fail;
  fi;

  new:=Orb(GeneratorsOfSemigroup(SupersemigroupOfIdeal(I)), pt, LambdaAct(I),
   record);
  Enumerate(new);
  
  ht:=o!.ht;
  for i in [1..Length(new)] do 
    HTAdd(ht, new[i], i+len);
  od;
  
  o!.scc_reps[Length(o!.scc)+1]:=x;
  
  # JDM probably don't store these things in <o> since they are already in <new>
  # or remove them from the individual orbits...
  Append(o!.scc_lookup, OrbSCCLookup(new)+Length(o!.scc));
  Append(o!.scc, OrbSCC(new)+len);  
  Append(o!.schreiergen, new!.schreiergen);
  Add(o!.schreierpos, fail);
  for i in [2..Length(new)] do 
    Add(o!.schreierpos, new!.schreierpos[i]+len);
  od;
  Append(o!.orbitgraph, new!.orbitgraph+len);

  o!.orbits[Length(o!.orbits)+1]:=new;
  o!.lens[Length(o!.orbits)]:=Length(new);

  nrorb := Length(o!.orbits);  
  o!.orbschreierpos[nrorb] := pos;
  o!.orbschreiergen[nrorb] := gen;
  
  if pos<>fail then 
    # find the component containing <pos>
    cmp:=1;
    while pos>Length(o!.orbits[cmp]) do
      pos:=pos-Length(o!.orbits[cmp]);
      cmp:=cmp+1;
    od;
    o!.orbschreiercmp[nrorb] := cmp;
  else 
    o!.orbschreiercmp[nrorb] := fail;
  fi;

  # jj assume that if a generator is passed into UpadateIdealLambdaOrb then
  # pos = the index of the generator and ind <> fail.
  if ind <> fail then
    o!.orbtogen[nrorb] := ind;
  fi;
  return len+1;
end);

#

InstallMethod(RhoOrb, "for an acting semigroup ideal", 
[IsActingSemigroup and IsSemigroupIdeal],
function(I)
  local record, htopts, fam;
 
  record:=rec();
  record.orbits:=[[fail]];      record.lens:=[1];    
  record.parent:=I;             record.scc:=[[1]];       
  record.scc_reps:=[fail,];     record.scc_lookup:=[1];
  record.schreiergen:=[fail];   record.schreierpos:=[fail];
  record.orbitgraph:=[[]];      
  record.gens:=GeneratorsOfSemigroup(SupersemigroupOfIdeal(I));
  record.orbschreierpos := [];
  record.orbschreiergen := [];
  record.orbschreiercmp := [];
  record.orbtogen := [];

  htopts:=ShallowCopy(RhoOrbOpts(I)); 
  htopts.treehashsize:=I!.opts.hashlen.M;
  record.ht:=HTCreate(RhoFunc(I)(Representative(I)), htopts);
  
  fam:=CollectionsFamily(FamilyObj(RhoFunc(I)(Representative(I))));
  return Objectify(NewType(fam, IsIdealRhoOrb), record);
end);

# assumes that <pt> is not in <o> already...

InstallGlobalFunction(UpdateIdealRhoOrb, 
function(o, pt, x, pos, gen, ind)
  local I, record, len, new, ht, nrorb, cmp, i;

  I:=o!.parent; 
  record:=ShallowCopy(RhoOrbOpts(I));
  
  record.schreier:=true;        record.orbitgraph:=true;
  record.storenumbers:=true;    record.log:=true;
  record.parent:=I;             record.treehashsize:=I!.opts.hashlen.M;
 
  len:=Length(o);

  if len<>0 then 
    record.gradingfunc:=function(new, x)
      return x in o;
    end;
    record.onlygrades:=function(x, data);
      return not x;
    end;
    record.onlygradesdata:=fail;
  fi;

  new:=Orb(GeneratorsOfSemigroup(SupersemigroupOfIdeal(I)), pt, RhoAct(I), record);
  Enumerate(new);
  
  ht:=o!.ht;
  for i in [1..Length(new)] do 
    HTAdd(ht, new[i], i+len);
  od;
  
  o!.scc_reps[Length(o!.scc)+1]:=x;
  
  # JDM probably don't store these things in <o> since they are already in <new>
  # or remove them from the individual orbits...
  Append(o!.scc_lookup, OrbSCCLookup(new)+Length(o!.scc));
  Append(o!.scc, OrbSCC(new)+len);  
  Append(o!.schreiergen, new!.schreiergen);
  Add(o!.schreierpos, fail);
  for i in [2..Length(new)] do 
    Add(o!.schreierpos, new!.schreierpos[i]+len);
  od;
  Append(o!.orbitgraph, new!.orbitgraph+len);

  o!.orbits[Length(o!.orbits)+1]:=new;
  o!.lens[Length(o!.orbits)]:=Length(new);

  nrorb := Length(o!.orbits);  
  o!.orbschreierpos[nrorb] := pos;
  o!.orbschreiergen[nrorb] := gen;
  
  if pos<>fail then 
    # find the component containing <pos>
    cmp:=1;
    while pos>Length(o!.orbits[cmp]) do
      pos:=pos-Length(o!.orbits[cmp]);
      cmp:=cmp+1;
    od;
    o!.orbschreiercmp[nrorb] := cmp;
  else
    o!.orbschreiercmp[nrorb] := fail;
  fi;

  # jj assume that if a generator is passed into UpadateIdealRhoOrb then
  # pos = the index of the generator and ind<>fail.
  if ind<>fail then
    o!.orbtogen[nrorb] := ind;
  fi;
  return len+1;
end);

#

InstallMethod(EvaluateWord, 
"for a semigroup ideal and a triple of words (Semigroups)",
[IsSemigroupIdeal, IsList],
function(I, w)
    local res, gens, i;

    if HasGeneratorsOfSemigroup(I) and IsPosInt(w[1]) then 
      return EvaluateWord(GeneratorsOfSemigroup(I), w);
    fi;

    gens:=GeneratorsOfSemigroup(SupersemigroupOfIdeal(I));
    res:=GeneratorsOfSemigroupIdeal(I)[AbsInt(w[2])]^SignInt(w[2]);
    
    for i in [1..Length(w[1])] do
      res:=gens[w[1][i]]*res;
    od;
    for i in [1..Length(w[3])] do
      res:=res*gens[w[3][i]];
    od;
    return res;
  end );

#

InstallMethod(EvaluateWord, 
"for a semigroup and a word (Semigroups)",
[IsSemigroup and HasGeneratorsOfSemigroup, IsList], 1, 
# to beat the methods for IsXCollection
function(S, w)
  return EvaluateWord(GeneratorsOfSemigroup(S), w);
end);

#

InstallMethod(TraceSchreierTreeForward, 
"for an inverse semigroup ideal orbit and a positive integer",
[IsInverseIdealOrb, IsPosInt],
function(o, i)
  local schreierpos, schreiergen, rightword, nr;
  
  schreierpos := o!.schreierpos;
  schreiergen := o!.schreiergen;
   
  rightword := [];
  
  while schreierpos[i] <> fail do
    Add(rightword, schreiergen[i]);
    i := schreierpos[i];
  od;

  if o!.orbtogen[i]>Length(GeneratorsOfSemigroupIdeal(o!.parent)) then 
    nr:=-o!.orbtogen[i]+Length(GeneratorsOfSemigroupIdeal(o!.parent));
  else
    nr:=o!.orbtogen[i];
  fi;

  return [ [], nr, Reversed(rightword)];
end);

#

InstallMethod(TraceSchreierTreeForward,
"for an ideal orbit and positive integer",
[IsIdealOrb, IsPosInt],
function(o, i)
  local orbschreierpos, orbschreiergen, orbschreiercmp, schreierpos, schreiergen, leftword, rightword, nr, j;

  orbschreierpos := o!.orbschreierpos;
  orbschreiergen := o!.orbschreiergen;
  orbschreiercmp := o!.orbschreiercmp;
  
  schreierpos := o!.schreierpos;
  schreiergen := o!.schreiergen;
   
  leftword := [];
  rightword := [];
  
  #find the component <nr> containing <i>
  nr:=1;
  j:=i;
  while j>Length(o!.orbits[nr]) do 
    j:=j-Length(o!.orbits[nr]);
    nr:=nr+1;
  od;
  
  # trace back to the start of the component
  while schreierpos[i] <> fail do
    Add(rightword, schreiergen[i]);
    i := schreierpos[i];
  od;

  while orbschreiergen[nr]<>fail do  
    Add(leftword, orbschreiergen[nr]);
    
    i:=orbschreierpos[nr];
    nr:=orbschreiercmp[nr];

    while schreierpos[i] <> fail do
      Add(rightword, schreiergen[i]);
      i := schreierpos[i];
    od;

  od;

  return [Reversed(leftword), o!.orbtogen[nr], Reversed(rightword)];
end);

#

# the arguments are a lambda/rho orbit of a parent semigroup and a number. jj
InstallGlobalFunction(SuffixOrb,
function(o, i)
  local out, scc, lookup, graph, adj, bool, x, z, y, newadj;

  scc := OrbSCC(o);
  lookup := OrbSCCLookup(o);
  graph := OrbitGraph(o);
  adj := [lookup[i]];
  bool := BlistList([1..Length(scc)], [lookup[i]]); 
  out := [lookup[i]];

  while adj <> [] do
    newadj := [];
    for x in adj do
      for y in scc[x] do
        for z in graph[y] do
          if not bool[lookup[z]] then
            bool[lookup[z]] := true;
            Add(out, lookup[z]);
            Add(newadj, lookup[z]);
          fi;
        od;
      od;
    od;
    adj := newadj;
  od;

  return out;
end);
# the first position of the returned word refers to the generators of the ideal
# corresponding to the position in the orbit of the point from which the <o[pos]>
# is obtained. For example, [1,2,3] means I.1*S.2*S.3.

#InstallMethod( TraceSchreierTreeForward, 
#"for an ideal orb and a position (Semigroups)",
#  [ IsIdealOrb, IsPosInt ],
#  function( o, pos )
#    local word;
#    word := [];
#    while o!.schreierpos[pos] <> fail do
#        Add(word,o!.schreiergen[pos]);
#        pos := o!.schreierpos[pos];
#    od;
#    Add(word, o!.genslookup[pos]);
#    return Reversed(word);
#  end );
#
##
#
#
##Usage: o = orbit of images; i = index of scc; j = element of scc[i].
#
## Notes: returns a word in the generators that takes o!.scc[i][1] to o[j] 
## assuming that j in scc[i]
#
#InstallMethod(TraceSchreierTreeOfSCCForward,
#"for an ideal orbit and two positive integers",
#[IsIdealOrb, IsPosInt, IsPosInt],
#function(o, i, j)
#  local tree, scc, word, parent;
#
#  tree:=SchreierTreeOfSCC(o, i);
#  scc:=OrbSCC(o)[i];
#
#  word := [];
#  parent := tree[2][j];
#  while parent  <> fail do
#    Add(word, tree[1][j]);
#    j := parent;
#    parent := tree[2][j];
#  od;
#  
#  Add(word, o!.genslookup[j]);
#  return Reversed(word);
#end);
#
#
#InstallMethod(TraceSchreierTreeOfSCCBack,
#"for an ideal orbit and two positive integers",
#[IsIdealOrb, IsPosInt, IsPosInt],
#function(o, i, j)
#  local tree, mult, scc, word, parent;
#
#  if not IsInvLambdaOrb(o) then
#    tree:=ReverseSchreierTreeOfSCC(o, i);
#    mult:=1;
#  else
#    tree:=SchreierTreeOfSCC(o, i);
#    mult:=-1;
#  fi;
#
#  scc:=OrbSCC(o)[i];
#
#  word := [];
#  parent := tree[2][j];
#  while parent <> fail do
#    Add(word, tree[1][j]);
#    j := parent;
#    parent := tree[2][j];
#  od;
#
#  return word*mult;
#end);
#
#
#
