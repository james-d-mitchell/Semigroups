//
// Semigroups package for GAP
// Copyright (C) 2018 James D. Mitchell
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

#ifndef SEMIGROUPS_SRC_BMAT8_H_
#define SEMIGROUPS_SRC_BMAT8_H_

#include "gapbind.h"
#include "libsemigroups/src/bmat.h"
#include "pkg.h"

using libsemigroups::BMat8;

// Register a subtype . . .
UInt T_BMAT8 = pkg_obj_subtype.register_subtype("BMat8");

// Convert from GAP matrix of blists to BMat8

BMat8* convert_from_gap_to_bmat8(gap_list_t list) {
  SEMIGROUPS_ASSERT(IS_LIST(list));
  SEMIGROUPS_ASSERT(LEN_LIST(list) > 0);
  SEMIGROUPS_ASSERT(IS_BLIST_REP(ELM_LIST(list, 1)));

  size_t dim = LEN_BLIST(ELM_LIST(list, 1));
  BMat8* x   = new BMat8();
  for (size_t i = 0; i < dim; i++) {
    Obj row = ELM_PLIST(list, i + 1);
    SEMIGROUPS_ASSERT(IS_BLIST_REP(row));
    SEMIGROUPS_ASSERT(LEN_BLIST(row) == dim);
    for (size_t j = 0; j < dim; j++) {
      if (ELM_BLIST(row, j + 1) == True) {
        // x.set(i, j, true);
      }
    }
  }
  return x;
}

// Install methods
GAP_CONSTRUCTOR_1_ARG(NEW_BMAT8, T_BMAT8, BMat8*, convert_from_gap_to_bmat8);
GAP_FUNC_METHOD_1_ARG(BMAT8_TO_INT, BMat8*, to_int, intobj_int);

#endif  // SEMIGROUPS_SRC_BMAT8_H_
