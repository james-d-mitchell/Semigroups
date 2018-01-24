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

#include <cxxabi.h>

#include <cstdlib>
#include <sstream>
#include <string>
#include <vector>

#include "src/compiled.h"
// TODO namespace

UInt T_PKG_OBJ = 0;
Obj  TheTypeTPkgObj;

Obj TPkgObjTypeFunc(Obj o) {
  return TheTypeTPkgObj;
}

typedef size_t t_pkg_obj_subtype_t;

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

inline t_pkg_obj_subtype_t t_pkg_obj_subtype(Obj o) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(o) == T_PKG_OBJ);
  return static_cast<t_pkg_obj_subtype_t>(
      reinterpret_cast<UInt>(ADDR_OBJ(o)[0]));
}

template <typename TClass> inline TClass t_pkg_obj_cpp_class(Obj o) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(o) == T_PKG_OBJ);
  return reinterpret_cast<TClass>(ADDR_OBJ(o)[1]);
}

class PkgObjSubtype {
  typedef std::function<void(Obj)> FUNCTION;

 public:
  PkgObjSubtype() : _next_subtype(0) {}

  t_pkg_obj_subtype_t register_subtype(std::string     name,
                                       FUNCTION const& free_func,
                                       FUNCTION const& save_func,
                                       FUNCTION const& load_func) {
    _names.push_back(name);
    _free_funcs.push_back(free_func);
    _save_funcs.push_back(save_func);
    _load_funcs.push_back(load_func);
    return _next_subtype++;
  }

  std::string name(Obj o) {
    SEMIGROUPS_ASSERT(TNUM_OBJ(o) == T_PKG_OBJ);
    return _names.at(t_pkg_obj_subtype(o));
  }

  void free(Obj o) {
    SEMIGROUPS_ASSERT(TNUM_OBJ(o) == T_PKG_OBJ);
    return _free_funcs.at(t_pkg_obj_subtype(o))(o);
  }

  void save(Obj o) {
    SEMIGROUPS_ASSERT(TNUM_OBJ(o) == T_PKG_OBJ);
    return _save_funcs.at(t_pkg_obj_subtype(o))(o);
  }

  void load(Obj o) {
    SEMIGROUPS_ASSERT(TNUM_OBJ(o) == T_PKG_OBJ);
    return _load_funcs.at(t_pkg_obj_subtype(o))(o);
  }

 private:
  t_pkg_obj_subtype_t      _next_subtype;
  std::vector<std::string> _names;
  std::vector<FUNCTION>    _free_funcs;
  std::vector<FUNCTION>    _save_funcs;
  std::vector<FUNCTION>    _load_funcs;
} PKG_OBJ_SUBTYPE_MANAGER;

template <typename T> std::string type_name() {
  int         status;
  std::string tname = typeid(T).name();
  char*       demangled_name =
      abi::__cxa_demangle(tname.c_str(), NULL, NULL, &status);
  if (status == 0) {
    tname = demangled_name;
    std::free(demangled_name);
  }
  return tname;
}

template <typename T>
t_pkg_obj_subtype_t REGISTER_PKG_OBJ(std::function<void(Obj)> save,
                                     std::function<void(Obj)> load) {
  t_pkg_obj_subtype_t st = PKG_OBJ_SUBTYPE_MANAGER.register_subtype(
      type_name<T>(),
      [&st](Obj x) -> void {
        SEMIGROUPS_ASSERT(t_pkg_obj_subtype(x) == st);
        delete t_pkg_obj_cpp_class<T*>(x);
      },
      save,
      load);
  return st;
}

// TODO figure out how to remove the ostringstream from here!
void TPkgObjPrintFunc(Obj o) {
  std::ostringstream stm;
  stm << o;
  Pr("<C++ class %s at %s>",
     (Int) PKG_OBJ_SUBTYPE_MANAGER.name(o).c_str(),
     (Int) stm.str().c_str());
}

// TODO Is the next one required?
// Obj TPkgObjCopyFunc(Obj o, Int mut) {
//  return o;
//}

void TPkgObjCleanFunc(Obj o) {}

Int TPkgObjIsMutableObjFuncs(Obj o) {
  return 1L;
}

void TPkgObjFreeFunc(Obj o) {
  PKG_OBJ_SUBTYPE_MANAGER.free(o);
}

void TPkgObjSaveFunc(Obj o) {
  SaveUInt(t_pkg_obj_subtype(o));
  PKG_OBJ_SUBTYPE_MANAGER.save(o);
}

void TPkgObjLoadFunc(Obj o) {
  ADDR_OBJ(o)[0] = (Obj) LoadUInt();
  PKG_OBJ_SUBTYPE_MANAGER.load(o);
}

#endif  // SEMIGROUPS_SRC_GAPBIND_H_
