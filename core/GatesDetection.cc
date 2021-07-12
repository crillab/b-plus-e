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
   For all literals, collect the set of literal obtained by unit
   propagation.

   @param[out] listPU, the vector where is stroe the result
*/
void GatesDetection::collectBinaryAdj(Solver &solver, vec<vec<Lit>> &listPU) {
  vec<Lit> &trail = solver.trail;
  int posTrail = trail.size();

  for (int i = 0; i < solver.nVars(); i++) {
    listPU.push();
    listPU.push(); // add both list

    if (solver.value(i) != l_Undef)
      continue;

    Lit l = mkLit(i, true);

    solver.newDecisionLevel();
    solver.uncheckedEnqueue(l);
    solver.propagate();

    for (int j = posTrail + 1; j < trail.size(); j++)
      listPU[toInt(l)].push(trail[j]);
    solver.cancelUntil(0);

    solver.newDecisionLevel();
    solver.uncheckedEnqueue(~l);
    solver.propagate();
    for (int j = posTrail + 1; j < trail.size(); j++)
      listPU[toInt(~l)].push(trail[j]);
    solver.cancelUntil(0);
  }
} // collectBinaryAdj

/**
   For all literals, collect the set of literal obtained by unit
   propagation.

   @param[in] solver, the SAT solver with the problem loaded
   @param[out] listPU, the vector where is stroe the result
   @param[in] l, the literal we want the adjacency list
*/
void GatesDetection::collectBinaryAdjLit(Solver &solver, vec<Lit> &listPU,
                                         Lit l) {
  vec<Lit> &trail = solver.trail;
  int posTrail = trail.size();
  if (solver.value(l) != l_Undef)
    return;

  solver.newDecisionLevel();
  solver.uncheckedEnqueue(l);
  CRef conf = solver.propagate();

  if (conf == CRef_Undef)
    for (int j = posTrail + 1; j < trail.size(); j++)
      listPU.push(trail[j]);
  solver.cancelUntil(0);

  if (conf != CRef_Undef && solver.value(l) == l_Undef)
    solver.uncheckedEnqueue(l);
} // collectBinaryAdjLit

/**
   Collect a set of binary equivalence w.r.t a adjacance matrix of
   literals.

   @param[in] solver, the SAT solver with the problem loaded
   @param[out] listOfOrGates, where we add the detected gates
   @param[in] l, the literal we want the adjacency list
*/
inline void
GatesDetection::collectBinaryEquivalence(Solver &solver,
                                         vec<vec<Lit>> &listOfOrGates, Lit l) {
  vec<int> flags;
  for (int i = 0; i < solver.nVars(); i++)
    flags.push(0);

  if (solver.value(l) != l_Undef)
    return;

  vec<Lit> tmpN;
  collectBinaryAdjLit(solver, tmpN, l);
  vec<Lit> tmpP;
  collectBinaryAdjLit(solver, tmpP, ~l);

  if (solver.value(l) != l_Undef || !tmpN.size() || !tmpP.size())
    return;

  for (int j = 0; j < tmpN.size(); j++)
    flags[var(tmpN[j])] = 1 + sign(tmpN[j]);
  for (int j = 0; j < tmpP.size(); j++) {
    if (!flags[var(tmpP[j])])
      continue; // not marked
    if (flags[var(tmpP[j])] + sign(tmpP[j]) == 2) {
      listOfOrGates.push();
      (listOfOrGates.last()).push(l);
      (listOfOrGates.last()).push(~tmpP[j]);
    }
  }

  for (int j = 0; j < tmpN.size(); j++)
    flags[var(tmpN[j])] = 0; // unmark
} // collectBinaryEquivalence

/**
   Search a gate such that the output is a given literal (not the
   variable).

   @param[in] solver, the SAT solver with the problem
   @param[out] og, the computed gate
   @param[in] l, the literal we want to use
   @param[in] occurrences, the occurrences list (give for a literal the place
   where it is in the CNF)
 */
void GatesDetection::searchOrGateFromLit(Solver &solver, vec<Lit> &og, Lit l,
                                         vec<vec<int>> &occurrences) {
  if (solver.value(l) != l_Undef)
    return;

  solver.newDecisionLevel();
  solver.uncheckedEnqueue(l);

  if (solver.propagate() != CRef_Undef) {
    solver.cancelUntil(0);
    solver.uncheckedEnqueue(~l);
    solver.propagate();
  } // litImplied
  else {
    vec<Lit> tmpLits;
    for (int j = solver.trail_lim[0] + 1; j < (solver.trail).size(); j++)
      tmpLits.push(solver.trail[j]);
    solver.cancelUntil(0);
    solver.newDecisionLevel();
    solver.uncheckedEnqueue(~l);

    vec<Lit> litUncheck;
    // search
    CRef confl = CRef_Undef;
    for (int j = 0; j < tmpLits.size() && confl == CRef_Undef; j++) {
      Lit tl = tmpLits[j];

      if (solver.value(tl) == l_True || !occurrences[toInt(tl)].size() ||
          !occurrences[toInt(~tl)].size())
        continue;
      if (solver.value(tl) == l_False)
        confl = solver.reason(var(tl));
      else {
        solver.newDecisionLevel();
        solver.uncheckedEnqueue(tl);
        confl = solver.propagate();
      }
    }

    if (confl != CRef_Undef) {
      solver.analyzeDecision(confl, litUncheck); // reduce
      if (litUncheck.size() == 0 ||
          (litUncheck.size() == 1 && litUncheck[0] == ~l)) {
        if (solver.value(l) == l_Undef)
          solver.uncheckedEnqueue(l);
      } else {
        // search l
        bool isInside = false;
        for (int j = 0; j < litUncheck.size() && !isInside; j++)
          if (var(litUncheck[j]) == var(l)) {
            isInside = true;
            litUncheck[j] = litUncheck.last();
            litUncheck.pop();
          }

        if (isInside) {
          og.push(~l);
          for (int j = 0; j < litUncheck.size(); j++)
            og.push(~litUncheck[j]);
          assert(og.size() > 1);
        }
      }
    }
    solver.cancelUntil(0);
  }
} // searchOrGateFromLit

/**
   Collect set of OR gates

   @param[in] solver, the SAT solver with the problem loaded
   @param[out] listOfOrGates, where we add the detected gates
*/
void GatesDetection::collectOrGates(Solver &solver,
                                    vec<vec<Lit>> &listOfOrGates) {
  vec<vec<int>> occurrences;
  for (int i = 0; i < (solver.nVars() << 1); i++)
    occurrences.push();
  for (int i = 0; i < solver.clauses.size(); i++) {
    Clause &c = solver.ca[solver.clauses[i]];
    for (int j = 0; j < c.size(); j++)
      occurrences[toInt(c[j])].push(i);
  }

  vec<Lit> unitLits;
  for (int i = 0; i < solver.nVars(); i++) {
    if (solver.value(i) != l_Undef || isProtected[i])
      continue;

    Lit l = mkLit(i, false);
    if (!occurrences[toInt(l)].size() || !occurrences[toInt(~l)].size())
      continue;

    for (int b = 0; b < 2; b++) {
      l = ~l; // we change the phase

      vec<Lit> og;
      searchOrGateFromLit(solver, og, l, occurrences);
      if (og.size()) {
        listOfOrGates.push();
        og.copyTo(listOfOrGates.last());
      }
    }
  }
} // collectOrGates

/**
   Research in the formula stored in the solver given in paremeter a
   set of gates.

   @param[in] solver, the solver
   @param[out] gates, the set of gates computed
 */
void GatesDetection::collectGates(Solver &solver, vec<vec<Lit>> &gates,
                                  vec<Var> &protectedVar) {
  for (int v = 0; v < solver.nVars(); v++)
    isProtected.push(false);
  for (int i = 0; i < protectedVar.size(); i++)
    isProtected[protectedVar[i]] = true;
  for (int v = 0; v < solver.nVars(); v++)
    if (!isProtected[v])
      collectBinaryEquivalence(solver, gates, mkLit(v, false));
  collectOrGates(solver, gates);
} // collectGates
