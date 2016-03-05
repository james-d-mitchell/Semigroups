############################################################################
##
#W  semipbr.gi
#Y  Copyright (C) 2015                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################

#TODO IsomorphismSemigroup for IsBooleanMatSemigroup
#
# This file contains methods for semigroups of PBRs.

#############################################################################
## ?. Random
#############################################################################

InstallMethod(RandomSemigroupCons,
"for IsPBRSemigroup, pos int, int, int, int",
[IsPBRSemigroup, IsPosInt, IsInt, IsInt, IsInt],
function(filt, nrgens, deg, dummy1, dummy2)
  return Semigroup(List([1 .. nrgens], i -> RandomPBR(deg)));
end);

InstallMethod(RandomMonoidCons,
"for IsPBRMonoid, pos int, int, int, int",
[IsPBRMonoid, IsPosInt, IsInt, IsInt, IsInt],
function(filt, nrgens, deg, dummy1, dummy2)
  return Monoid(List([1 .. nrgens], i -> RandomPBR(deg)));
end);

InstallMethod(RandomInverseSemigroupCons,
"for IsPBRSemigroup, pos int, int, int, int",
[IsPBRSemigroup, IsPosInt, IsInt, IsInt, IsInt],
function(filt, nrgens, deg, dummy1, dummy2)
  return SEMIGROUPS.DefaultRandomInverseSemigroup(filt, nrgens, deg);
end);

InstallMethod(RandomInverseMonoidCons,
"for IsPBRMonoid, pos int, int, int, int",
[IsPBRMonoid, IsPosInt, IsInt, IsInt, IsInt],
function(filt, nrgens, deg, dummy1, dummy2)
  return SEMIGROUPS.DefaultRandomInverseMonoid(filt, nrgens, deg);
end);

InstallMethod(FullPBRMonoid, "for a positive integer",
[IsPosInt],
function(n)
  local gens;

  gens := [[PBR([[]], [[1]]), PBR([[-1, 1]], [[1]]),
            PBR([[-1]], [[]]), PBR([[-1]], [[1]]),
            PBR([[-1]], [[-1, 1]])],

           [PBR([[], [-1]], [[2], [-2, 1]]),
            PBR([[-2, 1], [-1]], [[2], []]),
            PBR([[-1, 2], [-2]], [[1], [2]]),
            PBR([[-1], [-2]], [[1], [-2, 2]]),
            PBR([[-2], [2]], [[1], [2]]),
            PBR([[-2], [-1]], [[1], [1, 2]]),
            PBR([[-2], [-1]], [[1], [2]]),
            PBR([[-2], [-1]], [[1], [-2]]),
            PBR([[-2], [-1]], [[2], [1]]),
            PBR([[-2], [-2, -1]], [[1], [2]])]];

  if n > 2 then
    ErrorNoReturn("Semigroups: FullPBRMonoid: usage,\n",
                  "the argument <n> must be at most 2,");
  fi;
  return Monoid(gens[n]);
end);

InstallMethod(SemigroupViewStringPrefix, "for a pbr semigroup",
[IsPBRSemigroup], S -> "\>pbr\< ");

InstallMethod(SemigroupViewStringSuffix, "for a pbr semigroup",
[IsPBRSemigroup],
function(S)
  return Concatenation("\>degree \>",
                       ViewString(DegreeOfPBRSemigroup(S)),
                       "\<\< ");
end);

InstallMethod(DegreeOfPBRSemigroup,
"for a PBR semigroup",
[IsPBRSemigroup],
function(S)
  return DegreeOfPBR(Representative(S));
end);

# fall back method via a transformation semigroup

InstallMethod(IsomorphismSemigroup, "for IsPBRSemigroup and a semigroup",
[IsPBRSemigroup, IsSemigroup], SEMIGROUPS.DefaultIsomorphismSemigroup);

InstallMethod(IsomorphismSemigroup,
"for IsPBRSemigroup and a transformation semigroup",
[IsPBRSemigroup, IsTransformationSemigroup],
function(filt, S)
  local deg, T;

  deg := Maximum(1, DegreeOfTransformationSemigroup(S));
  T := Semigroup(List(GeneratorsOfSemigroup(S), x -> AsPBR(x, deg)));
  UseIsomorphismRelation(S, T);

  return MagmaIsomorphismByFunctionsNC(S,
                                       T,
                                       x -> AsPBR(x, deg),
                                       AsTransformation);
end);

InstallMethod(IsomorphismSemigroup,
"for IsPBRSemigroup and a bipartition semigroup",
[IsPBRSemigroup, IsBipartitionSemigroup],
function(filt, S)
  local T;

  T := Semigroup(List(GeneratorsOfSemigroup(S), AsPBR));
  UseIsomorphismRelation(S, T);

  return MagmaIsomorphismByFunctionsNC(S,
                                       T,
                                       AsPBR,
                                       AsBipartition);
end);

InstallMethod(IsomorphismMonoid, "for IsPBRMonoid and a semigroup",
[IsPBRMonoid, IsSemigroup], SEMIGROUPS.DefaultIsomorphismMonoid);

InstallMethod(IsomorphismMonoid, "for IsPBRMonoid and a monoid",
[IsPBRMonoid, IsMonoid],
function(filter, S)
  return IsomorphismSemigroup(IsPBRSemigroup, S);
end);
