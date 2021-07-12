
/*-
 * b-plus-e
 * %%
 * Copyright (C) 2021 Artois University and CNRS
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * Contributors:
 *   *   CRIL - initial API and implementation
 */
#ifndef GLUCOSE_SOLVER_DEFINABLE_DETECTION
#define GLUCOSE_SOLVER_DEFINABLE_DETECTION

#include <cstring>

namespace Glucose {
class DefinableDetection {
  vec<Lit> unitLit;
  vec<bool> isProtected;

  struct coupleLit {
    Lit l;
    int nbOcc;
  };
  struct coupleVar {
    Var v;
    int nbOcc;
  };

  static int gt_coupleLit(const void *occ1, const void *occ2) {
    return ((coupleLit *)occ1)->nbOcc - ((coupleLit *)occ2)->nbOcc;
  }
  static int lt_coupleLit(const void *occ1, const void *occ2) {
    return ((coupleLit *)occ2)->nbOcc - ((coupleLit *)occ1)->nbOcc;
  }
  static int gt_coupleVar(const void *occ1, const void *occ2) {
    return ((coupleVar *)occ1)->nbOcc - ((coupleVar *)occ2)->nbOcc;
  }
  static int lt_coupleVar(const void *occ1, const void *occ2) {
    return ((coupleVar *)occ2)->nbOcc - ((coupleVar *)occ1)->nbOcc;
  }

  inline void sortSelectorsDummy(vec<Lit> &selectors, vec<Lit> &assums) {
    for (int i = selectors.size() - 1; i >= 0; i--)
      assums.push(selectors[i]);
  } // sortSelectorsDummy

  inline Lit selectAndRemove(vec<Lit> &set) {
    assert(set.size());
    Lit l = set.last();
    set.pop();

    return l;
  } // selectAndRemove

  void sortSelectorsOccDesc(Solver &solver, vec<Lit> &selectors,
                            vec<Lit> &assums, int initNbVar,
                            vec<vec<Lit>> &cls);

  static int sortDesc(const void *a, const void *b) {
    return *(int *)a - *(int *)b;
  }
  static int sortOccListDesc(const void *occ1, const void *occ2) {
    return *(1 + (int *)occ2) - *(1 + (int *)occ1);
  }
  void sortSelectorsTautologyGeneration(Solver &solver, vec<Lit> &selectors,
                                        int initVarNum, vec<Lit> &assums,
                                        vec<vec<Lit>> &cls);

  void addShiftFormula(Solver &solver, vec<vec<Lit>> &cls, int shift);
  void addSelectedEquivalence(Solver &solver, vec<Var> &v1, vec<Var> &v2,
                              vec<Lit> &selectors);

  void constructive(Solver &s, vec<Lit> &assums, int nbVar, vec<Var> &i,
                    vec<Var> &o, int limitC, vec<vec<Lit>> &gates);

public:
  inline vec<Lit> &getUnitLit() { return unitLit; }

  void computeBackBone(Solver &solver, vec<lbool> &currentModel);
  void collectBiPartition(vec<vec<Lit>> &cls, int nbV, vec<Var> &i, vec<Var> &o,
                          int nbConfl, const char *defSort, vec<vec<Lit>> &g,
                          vec<Var> &protectedVar);
};
} // namespace Glucose

#endif
