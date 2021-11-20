//
// Semigroups package for GAP
// Copyright (C) 2016 James D. Mitchell
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//

// This file contains everything in the kernel module for the Semigroups
// package that involves GAP directly, i.e. importing functions/variables from
// GAP and declaring functions for GAP etc.

#ifndef SEMIGROUPS_SRC_PKG_H_
#define SEMIGROUPS_SRC_PKG_H_

#if (defined(__GNUC__) && __GNUC__ < 5 \
     && !(defined(__clang__) || defined(__INTEL_COMPILER)))
#error "GCC version 5.0 or higher is required"
#endif

// Inclusion of <cstdef> appears to be required to prevent travis from issuing
// the warning:
//
//     /usr/include/c++/5/cstddef:51:11: error: ‘::max_align_t’ has not been
//     declared
//
// according to:
//
// https://stackoverflow.com/questions/35110786/how-to-fix-the-error-max-align-t

#include <cstddef>

#include <iostream>
#include <vector>

#include "compiled.h"

#include "rnams.h"
#include "semigroups-debug.h"

extern UInt T_BIPART;
extern UInt T_BLOCKS;

// Imported types and functions from the library
extern Obj SEMIGROUPS;
extern Obj HTValue;
extern Obj HTAdd;
extern Obj Pinfinity;
extern Obj Ninfinity;
extern Obj IsInfinity;
extern Obj IsNegInfinity;
extern Obj IsBooleanMat;
extern Obj BooleanMatType;
extern Obj MaxPlusMatrixType;
extern Obj IsMaxPlusMatrix;
extern Obj MinPlusMatrixType;
extern Obj IsMinPlusMatrix;
extern Obj TropicalMinPlusMatrixType;
extern Obj IsTropicalMinPlusMatrix;
extern Obj TropicalMaxPlusMatrixType;
extern Obj IsTropicalMaxPlusMatrix;
extern Obj ProjectiveMaxPlusMatrixType;
extern Obj IsProjectiveMaxPlusMatrix;
extern Obj IsNTPMatrix;
extern Obj NTPMatrixType;
extern Obj IsIntegerMatrix;
extern Obj IntegerMatrixType;
extern Obj IsPBR;
extern Obj DegreeOfPBR;
extern Obj TYPES_PBR;
extern Obj TYPE_PBR;

extern Obj TYPE_BIPART;
extern Obj TYPES_BIPART;
extern Obj GeneratorsOfMagma;
extern Obj LARGEST_MOVED_PT_TRANS;

extern Obj IsSemigroup;
extern Obj IsSemigroupIdeal;
extern Obj IsActingSemigroup;

extern Obj PositionCanonical;

#endif  // SEMIGROUPS_SRC_PKG_H_
