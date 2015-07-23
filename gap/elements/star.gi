#############################################################################
##
#W  star.gi
#Y  Copyright (C) 2015                                   James D. Mitchell
##
##  Licensing information can be found in the README file of this package.
##
#############################################################################
##

# star

InstallMethod(Star, "for an associative element with star",
[IsAssociativeElementWithStar],
function(elm)
  elm := StarOp(elm);
  MakeImmutable(elm);
  return elm;
end);