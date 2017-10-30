

// Orbits
template <typename T> struct VectorEqual {
  bool operator()(std::vector<T>* pt1, std::vector<T>* pt2) const {
    return *pt1 == *pt2;
  }
};

template <typename T> struct VectorHash {
  size_t operator()(std::vector<T> const* vec) const {
    size_t seed = 0;
    for (auto const& x : *vec) {
      seed ^= x + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    }
    return seed;
  }
};

typedef Obj gap_orb_t;

gap_orb_t semi_obj_init_orb(gap_semigroup_t so) {
  CHECK_SEMI_OBJ(so);
  initRNams();

  en_semi_obj_t es   = semi_obj_get_en_semi(so);
  en_semi_t     type = en_semi_get_type(es);

  // todo: bipart
  if (type == TRANS2) {
    Semigroup*                     semi_cpp = en_semi_get_semi_cpp(es);
    typedef std::vector<u_int16_t> point_type;
    auto act = [](Transformation<u_int16_t>* t, point_type* pt, point_type* tmp)
        -> point_type* { return t->lvalue(pt, tmp); };
    std::vector<Transformation<u_int16_t>*> gens;
    gens.reserve(semi_cpp->nrgens());
    for (size_t i = 0; i < semi_cpp->nrgens(); ++i) {
      gens.push_back(static_cast<Transformation<u_int16_t>*>(
          semi_cpp->gens(i)->really_copy()));
    }

    auto copier = [](point_type* pt) -> point_type* {
      return new point_type(*pt);
    };

    Orb<Transformation<u_int16_t>,
        point_type*,
        VectorHash<u_int16_t>,
        VectorEqual<u_int16_t>>* orb = new Orb(gens, act, copier);

    point_type* x   = new point_type();
    point_type* tmp = new point_type();
    for (size_t i = 0; i < gens[0]->degree(); ++i) {
      x->push_back(i);
    }

    for (size_t i = 0; i < gens.size(); ++i) {
      gens[i]->lvalue(x, tmp);
      orb->add_seed(tmp);
    }

    // Use OBJ_CLASS instead
    Obj o          = NewBag(T_SEMI, 2 * sizeof(Obj));
    ADDR_OBJ(o)[0] = reinterpret_cast<Obj>(T_SEMI_SUBTYPE_ORB);
    ADDR_OBJ(o)[1] = reinterpret_cast<Obj>(o);
    AssPRec(so, RNamName("NewLambdaOrb"), o);
    return o;
  } else {
    gap_list_t gens = semi_obj_get_gens(so);
    SEMIGROUPS_ASSERT(LEN_LIST(gens) > 0);
    ErrorQuit("ORB_SIZE: the argument must be a transformation or partial perm "
              "semigroup, not a %s",
              (Int) TNAM_OBJ(ELM_LIST(gens, 1)),
              0L);
    return 0L;
  }
}

Orb* semi_obj_get_orb(gap_semigroup_t so) {
  // TODO add assertions
  if (!IsbPRec(so, RNamName("NewLambdaOrb"))) {
    semi_obj_init_orb(so);
  }
  return CLASS_OBJ<Orb*>(ElmPRec(so, RNamName("NewLambdaOrb"));
}

gap_int_t AC_SEMI_L_ORB_SIZE(gap_semigroup_t so) {
  Orb* o = semi_obj_get_orb(so);
  return INTOBJ_INT(o->size());
}
