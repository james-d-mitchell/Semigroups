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

#ifndef SEMIGROUPS_SRC_CONG_H_
#define SEMIGROUPS_SRC_CONG_H_

#include <string>
#include <vector>

#include "gapbind.h"
#include "libsemigroups/src/cong.h"

#include "src/compiled.h"

using libsemigroups::Congruence;
using libsemigroups::Element;
using libsemigroups::word_t;
using libsemigroups::relation_t;

static std::vector<relation_t> to_vector_relations(Obj list) {
  SEMIGROUPS_ASSERT(IS_LIST(list));

  std::vector<relation_t> out;
  out.reserve(LEN_LIST(list));
  word_t lhs, rhs;
  for (size_t i = 1; i <= (size_t) LEN_LIST(list); i++) {
    SEMIGROUPS_ASSERT(IS_LIST(ELM_LIST(list, i)));
    Obj rel = ELM_LIST(list, i);
    lhs     = to_vector<size_t, to_vector_index<size_t>>(ELM_LIST(rel, 1));
    rhs     = to_vector<size_t, to_vector_index<size_t>>(ELM_LIST(rel, 2));
    out.push_back(make_pair(lhs, rhs));
  }
  return out;
}

// Register a subtype . . .
const UInt T_CONG =
    REGISTER_PKG_OBJ<Congruence<>>([](Obj o) -> void { std::cout << "LOL"; },
                                   [](Obj o) -> void { std::cout << "LOL"; });

// Congruence methods . . .
template <class TElementType>
static Obj
CONG_NEW_LIST(Obj self, Obj nrgens, Obj genpairs, Obj extra, Obj type) {
  SEMIGROUPS_ASSERT(IS_INTOBJ(nrgens));
  SEMIGROUPS_ASSERT(IS_LIST(genpairs));
  SEMIGROUPS_ASSERT(IS_LIST(extra));
  SEMIGROUPS_ASSERT(IS_STRING(type));
  // TODO there are basically no checks here
  return new_t_pkg_obj(
      T_CONG,
      new Congruence<TElementType>(std::string(CSTR_STRING(type)),
                                   INT_INTOBJ(nrgens),
                                   to_vector_relations(genpairs),
                                   to_vector_relations(extra)));
}

template <class TElementType> static Obj CONG_NR_CLASSES(Obj self, Obj cong) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(cong) == T_PKG_OBJ
                    && t_pkg_obj_subtype(cong) == T_CONG);
  return INTOBJ_INT(
      t_pkg_obj_cpp_class<Congruence<TElementType>*>(cong)->nr_classes());
}

template <class TElementType>
static Obj CONG_SET_REPORT(Obj self, Obj cong, Obj val) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(cong) == T_PKG_OBJ
                    && t_pkg_obj_subtype(cong) == T_CONG);
  t_pkg_obj_cpp_class<Congruence<TElementType>*>(cong)->set_report(
      BOOL_BOOLOBJ(val));
  return 0L;
}

REGISTER(CONG_NEW_LIST<Element*>);
REGISTER(CONG_SET_REPORT<Element*>);
REGISTER(CONG_NR_CLASSES<Element*>);

#endif  // SEMIGROUPS_SRC_CONG_H_
