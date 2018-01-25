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
#include <functional>
#include <sstream>
#include <string>
#include <vector>

#include "src/compiled.h"

// namespace gapbind {

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

static class PkgObjSubtype {
  typedef std::function<void(Obj)> FUNCTION;

 public:
  PkgObjSubtype() : _next_subtype(0) {}
  // TODO init other data members

  t_pkg_obj_subtype_t register_subtype(std::string     name,
                                       FUNCTION const& free_func,
                                       FUNCTION const& save_func,
                                       FUNCTION const& load_func) {
    // TODO check that the name is not already registered
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

  std::vector<StructGVarFunc> GVAR_FUNCS;

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

// Register a new subtype for the package T_NUM, with save, load, and free
// functions specified. Returns the new subtype.
template <typename T>
t_pkg_obj_subtype_t
REGISTER_PKG_OBJ(std::function<void(Obj)> save,
                 std::function<void(Obj)> load,
                 std::function<void(Obj)> free = [](Obj x) -> void {
                   delete t_pkg_obj_cpp_class<T*>(x);
                 }) {
  t_pkg_obj_subtype_t st = PKG_OBJ_SUBTYPE_MANAGER.register_subtype(
      type_name<T>(), save, load, free);
  return st;
}

// Register functions

template <typename R, typename... Types>
constexpr std::integral_constant<unsigned, sizeof...(Types)>
ArgumentCount(R (*f)(Types...)) {
  return std::integral_constant<unsigned, sizeof...(Types)>{};
}

typedef Obj (*GVarFunc)(/*arguments*/);

char const PARAMS[] = "abcdefghijklmnopqrstuvxyz";

char const* params(size_t nr) {
  SEMIGROUPS_ASSERT(nr < 26);
  std::string source;
  if (nr > 0) {
    for (size_t i = 0; i < nr - 1; ++i) {
      source += PARAMS[i] + std::string(", ");
    }
    source += PARAMS[nr - 1];
  }
  char* out = new char[source.size() + 1];  // we need extra char for NUL
  memcpy(out, source.c_str(), source.size() + 1);
  return out;
}

// The next function changes FUNC<PARAM> to PARAM_FUNC, and is probably
// extremely fragile.
static char const* convert_template_name(char const* c) {
  if (c == nullptr) {
    return c;
  }
  std::string source(c);
  size_t      first = source.find_first_of("<");
  if (first == std::string::npos) {
    return c;
  }
  size_t      last = source.find_last_of(">");
  std::string tp   = source.substr(first + 1, last - first - 1);
  source           = tp + "_" + source.substr(0, first);
  // Convert to upper case
  std::locale loc;
  for (size_t i = 0; i < source.length(); ++i) {
    source[i] = std::toupper(source[i], loc);
  }
  char* out = new char[source.size() + 1];  // we need extra char for NUL
  memcpy(out, source.c_str(), source.size() + 1);
  return out;
}

template <typename TFunctionType>
bool REGISTER_PKG_OBJ_FUNC(char const*    fname,
                           char const*    name,
                           TFunctionType* func,
                           Int            nparam) {
  std::string srcfile   = std::string(fname) + ":Func" + std::string(name);
  char*       c_srcfile = new char[srcfile.size() + 1];
  memcpy(c_srcfile, srcfile.c_str(), srcfile.size() + 1);
  PKG_OBJ_SUBTYPE_MANAGER.GVAR_FUNCS.push_back({convert_template_name(name),
                                                nparam,
                                                params(nparam),
                                                (GVarFunc) func,
                                                c_srcfile});
  return true;
}

#if defined(__COUNTER__) && (__COUNTER__ + 1 == __COUNTER__ + 0)
#define COUNTER __COUNTER__
#else
#define COUNTER __LINE__
#endif

#define TOKENPASTE(x, y) x##y
#define TOKENPASTE2(x, y) TOKENPASTE(x, y)
#define GAPBIND_PRIVATE_UNIQUE_ID int TOKENPASTE2(nothing, __COUNTER__) =

#define REGISTER(func)                             \
  GAPBIND_PRIVATE_UNIQUE_ID REGISTER_PKG_OBJ_FUNC( \
      __FILE__, #func, func, decltype(ArgumentCount(func))::value - 1)
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

// Default methods . . .
template <typename TElementType> static Obj EQUAL(Obj self, Obj x, Obj y) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_PKG_OBJ);
  SEMIGROUPS_ASSERT(TNUM_OBJ(y) == T_PKG_OBJ);
  SEMIGROUPS_ASSERT(t_pkg_obj_subtype(x) == t_pkg_obj_subtype(y));
  return (std::equal_to<TElementType>{}(*t_pkg_obj_cpp_class<TElementType*>(x),
                                        *t_pkg_obj_cpp_class<TElementType*>(y))
              ? True
              : False);
}

template <typename TElementType> static Obj LESS(Obj self, Obj x, Obj y) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_PKG_OBJ);
  SEMIGROUPS_ASSERT(TNUM_OBJ(y) == T_PKG_OBJ);
  SEMIGROUPS_ASSERT(t_pkg_obj_subtype(x) == t_pkg_obj_subtype(y));
  return (*t_pkg_obj_cpp_class<TElementType*>(x)
                  < *t_pkg_obj_cpp_class<TElementType*>(y)
              ? True
              : False);
}

template <typename TElementType> static Obj HASH(Obj self, Obj x) {
  SEMIGROUPS_ASSERT(TNUM_OBJ(x) == T_PKG_OBJ);
  return INTOBJ_INT(
      std::hash<TElementType>{}(*t_pkg_obj_cpp_class<TElementType*>(x)));
}

// Declaring things for GAP . . .

//} // namespace gapbind

#endif  // SEMIGROUPS_SRC_GAPBIND_H_
