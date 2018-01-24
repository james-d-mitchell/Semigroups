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
#include "libsemigroups/src/bmat8.h"
#include "pkg.h"

using libsemigroups::BMat8;

// Register a subtype . . .
UInt T_BMAT8 = pkg_obj_subtype.register_subtype("BMat8", "bmat8.h");

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
static Obj BMAT8_NEW(Obj self) {
  return new_t_pkg_obj(T_BMAT8, new BMat8());
}

// REGISTER_WITH_GAP(NEW_BMAT8, T_BMAT8);

static Obj BMAT8_TO_INT(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(t_pkg_obj_subtype(x) == T_BMAT8);
  return INTOBJ_INT(t_pkg_obj_cpp_class<BMat8*>(x)->to_int());
}

static Obj BMAT8_SET(Obj self, Obj x, Obj i, Obj j, Obj val) {
  SEMIGROUPS_ASSERT(t_pkg_obj_subtype(x) == T_BMAT8);
  SEMIGROUPS_ASSERT(IS_INTOBJ(i));
  SEMIGROUPS_ASSERT(INT_INTOBJ(i) >= 1 && INT_INTOBJ(i) <= 8);
  SEMIGROUPS_ASSERT(IS_INTOBJ(j));
  SEMIGROUPS_ASSERT(INT_INTOBJ(j) >= 1 && INT_INTOBJ(j) <= 8);
  SEMIGROUPS_ASSERT(val == True || val == False);
  t_pkg_obj_cpp_class<BMat8*>(x)->set(
      INT_INTOBJ(i) - 1, INT_INTOBJ(j) - 1, val == True);
  return 0L;
}

static Obj BMAT8_GET(Obj self, Obj x, Obj i, Obj j) {
  SEMIGROUPS_ASSERT(t_pkg_obj_subtype(x) == T_BMAT8);
  SEMIGROUPS_ASSERT(IS_INTOBJ(i));
  SEMIGROUPS_ASSERT(INT_INTOBJ(i) >= 1 && INT_INTOBJ(i) <= 8);
  SEMIGROUPS_ASSERT(IS_INTOBJ(j));
  SEMIGROUPS_ASSERT(INT_INTOBJ(j) >= 1 && INT_INTOBJ(j) <= 8);
  return (t_pkg_obj_cpp_class<BMat8*>(x)->operator()(INT_INTOBJ(i) - 1,
                                                     INT_INTOBJ(j) - 1)
              ? True
              : False);
}

#endif  // SEMIGROUPS_SRC_BMAT8_H_
