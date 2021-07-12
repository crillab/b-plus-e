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

#include <iostream>

#include "core/Backbone.h"
#include "core/Dimacs.h"
#include "core/GatesDetection.h"
#include "core/Solver.h"
#include "core/SolverTypes.h"
#include "mtl/Alg.h"
#include "mtl/Heap.h"
#include "mtl/Sort.h"
#include "mtl/Vec.h"
#include "utils/System.h"

using namespace std;
using namespace Glucose;

/**
   Compute the backbone.
*/
void Backbone::computeBackBone(Solver &solver, vec<lbool> &currentModel) {
  double initTime = cpuTime();
  int cpt = (solver.trail).size();

  for (int v = 0; v < solver.nVars(); v++) {
    // l is implied?
    if (solver.value(v) != l_Undef || currentModel[v] == l_Undef)
      continue;
    Lit l = mkLit(v, currentModel[v] == l_False);

    if (!solver.solve(~l)) {
      if (solver.value(l) == l_Undef)
        solver.uncheckedEnqueue(l);
    } else {
      for (int i = v; i < solver.nVars(); i++)
        if (currentModel[i] != solver.model[i])
          currentModel[i] = l_Undef;
    }
  }

  printf("c\nc Backbone simplification\n");
  printf("c The number of unit literal found is: %d\n",
         (solver.trail).size() - cpt);
  printf("c Time to realize the backbone simplification: %lf\n",
         cpuTime() - initTime);
} // computeBackBone
