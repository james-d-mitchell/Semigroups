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

// TODO file description

#ifndef SEMIGROUPS_SRC_GAPBIND_H_
#define SEMIGROUPS_SRC_GAPBIND_H_

#include "src/compiled.h"

extern Obj T_PKG_OBJ; // for positional objects
// Obj T_PKG_CMP_OBJ = 0; // for component objects

Obj TheTypeTPkgObj;
Obj TPkgObjTypeFunc(Obj o) {
  return TheTypeTPkgObj;
}

typedef size_t t_pkg_obj_subtype_t;

// TODO namespace

class PkgObjSubtype {
 public:
  PkgObjSubtype() : _next_subtype(0) {}

  t_pkg_obj_subtype_t register_subtype() {
    return ++_next_subtype;
  }

 private:
  t_pkg_obj_subtype_t _next_subtype;
} pkg_obj_subtype;

// A T_PKG_POS_OBJ Obj in GAP is of the form:
//
//     [t_pkg_obj_subtype_t, pointer to C++ obj]

// Get a new GAP Obj containing a pointer to a C++ class of type TClass
template <typename TClass>
inline Obj new_t_pkg_obj(t_pkg_obj_subtype_t subtype, TClass* ptr) {
  Obj o          = NewBag(T_PKG_OBJ, 2 * sizeof(Obj));
  ADDR_OBJ(o)[0] = (Obj) subtype;
  ADDR_OBJ(o)[1] = reinterpret_cast<Obj>(ptr);
  return o;
}

template <typename TClass> inline TClass t_pkg_obj_cpp_class(Obj o) {
  return reinterpret_cast<TClass>(ADDR_OBJ(o)[1]);
}

inline t_pkg_obj_subtype_t t_pkg_obj_subtype(Obj o) {
  // SEMIGROUPS_ASSERT(TNUM_OBJ(o) == T_t_semi_obj);
  // TODO change the above to an error
  return static_cast<t_pkg_obj_subtype_t>(
      reinterpret_cast<UInt>(ADDR_OBJ(o)[1]));
}

// Functions for converting from C/C++ to GAP Obj's

inline Obj intobj_int(Int x) {
  return INTOBJ_INT(x);
}

// Functions for converting from GAP Obj's to C/C++

#define GAP_CONSTRUCTOR_1_ARG(NAME, SUBTYPE, CPPTYPE, ARG_GAP_TO_CPP) \
  Obj NAME(Obj self, Obj x) {                                         \
    return new_t_pkg_obj(SUBTYPE, new CPPTYPE(ARG_GAP_TO_CPP(x)));    \
  }

#define GAP_FUNC_METHOD_1_ARG(NAME, TYPE, METHOD, RETURN_CPP_TO_GAP)   \
  Obj NAME(Obj self, Obj x) {                                          \
    return RETURN_CPP_TO_GAP(t_semi_obj_cpp_class<TYPE>(x)->METHOD()); \
  }

#endif  // SEMIGROUPS_SRC_GAPBIND_H_
