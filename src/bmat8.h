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

using libsemigroups::BMat8;

// Register a subtype . . .
const UInt T_BMAT8 = REGISTER_PKG_OBJ<BMat8>(
    [](Obj o) -> void { SaveUInt8(t_pkg_obj_cpp_class<BMat8*>(o)->to_int()); },
    [](Obj o) -> void {
      ADDR_OBJ(o)[1] = reinterpret_cast<Obj>(new BMat8(LoadUInt8()));
    });

// Install methods
static Obj BMAT8_NEW(Obj self) {
  return new_t_pkg_obj(T_BMAT8, new BMat8());
}

static Obj BMAT8_SET(Obj self, Obj x, Obj i, Obj j, Obj val) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_PKG_OBJ
                    && t_pkg_obj_subtype(x) == T_BMAT8);
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
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_PKG_OBJ
                    && t_pkg_obj_subtype(x) == T_BMAT8);
  SEMIGROUPS_ASSERT(IS_INTOBJ(i));
  SEMIGROUPS_ASSERT(INT_INTOBJ(i) >= 1 && INT_INTOBJ(i) <= 8);
  SEMIGROUPS_ASSERT(IS_INTOBJ(j));
  SEMIGROUPS_ASSERT(INT_INTOBJ(j) >= 1 && INT_INTOBJ(j) <= 8);
  return (t_pkg_obj_cpp_class<BMat8*>(x)->operator()(INT_INTOBJ(i) - 1,
                                                     INT_INTOBJ(j) - 1)
              ? True
              : False);
}

static Obj BMAT8_TRANSPOSE(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_PKG_OBJ
                    && t_pkg_obj_subtype(x) == T_BMAT8);
  return new_t_pkg_obj(T_BMAT8,
                       new BMat8(t_pkg_obj_cpp_class<BMat8*>(x)->transpose()));
}

static Obj BMAT8_MULTIPLY(Obj self, Obj x, Obj y) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_PKG_OBJ
                    && t_pkg_obj_subtype(x) == T_BMAT8);
  SEMIGROUPS_ASSERT(TNUM_OBJ(y) == T_PKG_OBJ
                    && t_pkg_obj_subtype(y) == T_BMAT8);
  return new_t_pkg_obj(T_BMAT8,
                       new BMat8((*t_pkg_obj_cpp_class<BMat8*>(x))
                                 * (*t_pkg_obj_cpp_class<BMat8*>(y))));
}

static Obj BMAT8_ONE(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_PKG_OBJ
                    && t_pkg_obj_subtype(x) == T_BMAT8);
  return new_t_pkg_obj(T_BMAT8,
                       new BMat8(t_pkg_obj_cpp_class<BMat8*>(x)->one()));
}

static Obj BMAT8_RANDOM(Obj self, Obj dim) {
  SEMIGROUPS_ASSERT(IS_INTOBJ(dim));
  SEMIGROUPS_ASSERT(INT_INTOBJ(dim) >= 1 && INT_INTOBJ(dim) <= 8);
  return new_t_pkg_obj(T_BMAT8, new BMat8(BMat8::random(INT_INTOBJ(dim))));
}

static Obj BMAT8_PRINT(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_PKG_OBJ
                    && t_pkg_obj_subtype(x) == T_BMAT8);
  Pr(std::to_string(*t_pkg_obj_cpp_class<BMat8*>(x)).c_str(), 0L, 0L);
  return 0L;
}

#endif  // SEMIGROUPS_SRC_BMAT8_H_
