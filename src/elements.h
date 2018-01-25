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

#ifndef SEMIGROUPS_SRC_ELEMENTS_H_
#define SEMIGROUPS_SRC_ELEMENTS_H_

#include <vector>

#include "gapbind.h"
#include "libsemigroups/src/elements.h"

using libsemigroups::Element;
using libsemigroups::BooleanMat;

// Register a subtype . . .
static const UInt T_ELEMENT =
    REGISTER_PKG_OBJ<Element>([](Obj o) -> void { std::cout << "LOL"; },
                              [](Obj o) -> void { std::cout << "LOL"; });

// Element methods . . .

static Obj ELEMENT_DEGREE(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_PKG_OBJ
                    && t_pkg_obj_subtype(x) == T_ELEMENT);
  return INTOBJ_INT(t_pkg_obj_cpp_class<Element*>(x)->degree());
}

static Obj ELEMENT_ONE(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_PKG_OBJ
                    && t_pkg_obj_subtype(x) == T_ELEMENT);
  return new_t_pkg_obj(T_ELEMENT, t_pkg_obj_cpp_class<Element*>(x)->identity());
}

REGISTER(HASH<Element>);
REGISTER(EQUAL<Element>);
REGISTER(ELEMENT_DEGREE);
REGISTER(ELEMENT_ONE);

// BooleanMat methods . . .
static Obj BOOLEANMAT_NEW(Obj self, Obj list) {
  SEMIGROUPS_ASSERT(IS_LIST(list));
  // SEMIGROUPS_ASSERT(LEN_LIST(list) > 8);
  SEMIGROUPS_ASSERT(IS_BLIST_REP(ELM_LIST(list, 1)));
  size_t             dim = LEN_BLIST(ELM_LIST(list, 1));
  std::vector<bool>* vec = new std::vector<bool>(dim * dim, false);
  for (size_t i = 0; i < dim; i++) {
    Obj blist = ELM_PLIST(list, i + 1);
    SEMIGROUPS_ASSERT(IS_BLIST_REP(blist));
    SEMIGROUPS_ASSERT(static_cast<size_t>(LEN_BLIST(blist)) == dim);
    for (size_t j = 0; j < dim; j++) {
      if (ELM_BLIST(blist, j + 1) == True) {
        (*vec)[i * dim + j] = true;
      }
    }
  }
  return new_t_pkg_obj(T_ELEMENT, new BooleanMat(vec));
}

// TODO The following could be more generic for ElementWithVectorData* in
// general
static Obj BOOLEANMAT_GET(Obj self, Obj x, Obj pos) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_PKG_OBJ
                    && t_pkg_obj_subtype(x) == T_ELEMENT);
  SEMIGROUPS_ASSERT(IS_INTOBJ(pos));
  try {
    return (t_pkg_obj_cpp_class<BooleanMat*>(x)->at(INT_INTOBJ(pos)) ? True
                                                                     : False);
  } catch (std::out_of_range& e) {
#ifdef SEMIGROUPS_KERNEL_DEBUG
    std::cerr << "exception std::out_of_range thrown "
                 "by libsemigroups::BooleanMat::at("
              << INT_INTOBJ(pos) << "): " << e.what() << std::endl;
#endif
    size_t deg = t_pkg_obj_cpp_class<BooleanMat*>(x)->degree();
    ErrorQuit("the second argument <pos> must be at most %d (not %d)",
              deg,
              INT_INTOBJ(pos));
    return 0L;  // to keep the compiler happy
  }
}

// TODO The following could be more generic for ElementWithVectorData* in
// general
static Obj BOOLEANMAT_MULTIPLY(Obj self, Obj x, Obj y) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_PKG_OBJ
                    && t_pkg_obj_subtype(x) == T_ELEMENT);
  SEMIGROUPS_ASSERT(TNUM_OBJ(y) == T_PKG_OBJ
                    && t_pkg_obj_subtype(y) == T_ELEMENT);

  BooleanMat* xx  = t_pkg_obj_cpp_class<BooleanMat*>(x);
  BooleanMat* yy  = t_pkg_obj_cpp_class<BooleanMat*>(y);
  size_t      dim = xx->degree();
  Element*    z   = new BooleanMat(new std::vector<bool>(dim * dim));
  z->redefine(xx, yy);
  return new_t_pkg_obj(T_ELEMENT, z);
}

REGISTER(BOOLEANMAT_MULTIPLY);
REGISTER(BOOLEANMAT_NEW);
REGISTER(BOOLEANMAT_GET);

#endif  // SEMIGROUPS_SRC_ELEMENTS_H_
