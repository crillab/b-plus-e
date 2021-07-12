
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
#ifndef GLUCOSE_SOLVER_GATES_DETECTION
#define GLUCOSE_SOLVER_GATES_DETECTION

#include "core/Solver.h"
#include <cstring>

namespace Glucose {
class GatesDetection {
private:
  Solver &solver;
  vec<bool> isProtected;

  vec<int> flags;
  void collectBinaryAdj(Solver &solver, vec<vec<Lit>> &listPU);
  void collectBinaryAdjLit(Solver &solver, vec<Lit> &listPU, Lit l);

public:
  GatesDetection(Solver &s) : solver(s) {}

  void searchOrGateFromLit(Solver &solver, vec<Lit> &og, Lit l,
                           vec<vec<int>> &occurrences);
  void collectGates(Solver &solver, vec<vec<Lit>> &gates,
                    vec<Var> &protectedVar);
  void collectBinaryEquivalence(Solver &solver, vec<vec<Lit>> &listOfOrGates,
                                Lit l);
  void collectOrGates(Solver &solver, vec<vec<Lit>> &listOfOrGates);
};
} // namespace Glucose

#endif
