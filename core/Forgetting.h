
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
#ifndef GLUCOSE_SOLVER_FORGETTING
#define GLUCOSE_SOLVER_FORGETTING

#include "mtl/Sort.h"
#include <iostream>

#include "SolverTypes.h"
#include "Solver.h"
#include "core/Utils.h"
#include "GatesDetection.h"

using namespace std;

namespace Glucose {
class Forgetting {
protected:
  struct LitOrderLt {
    const vec<double> &activity;
    const vec<bool> &markedOutputVars;
    bool operator()(Lit x, Lit y) const {
      if (markedOutputVars[var(x)] && !markedOutputVars[var(y)])
        return true;
      if (!markedOutputVars[var(x)] && markedOutputVars[var(y)])
        return false;
      return activity[var(x)] > activity[var(y)];
    }
    LitOrderLt(const vec<double> &act, const vec<bool> &m)
        : activity(act), markedOutputVars(m) {}
  };

private:
  Solver &solver;
  vec<uint64_t> hashKeyInit;
  vec<bool> markedOutputVars;
  vec<bool> markedAsForget;
  vec<char> markedLit; // must be 'always' false
  vec<unsigned int> stampSubsum;
  vec<vec<int>> watchNewCls;
  unsigned int stamp;

  vec<vec<int>> occurrences;
  vec<int> freePositionInClauses;

  // statistic variables
  int nbRemovedClauseVivi;
  int nbRemovedLitVivi;
  double timeVivi;
  int nbRemovedLitOccRm;
  double timeOccRm;

  // functions
  void initOccList(vec<CRef> &refClauses);
  void removeClauseOcc(int idx, vec<CRef> &refClauses);
  void addClauseOcc(vec<Lit> &lits, vec<CRef> &refClauses);
  void generateAllResolution(Var v, vec<vec<Lit>> &cls, vec<CRef> &refClauses);
  void removeSubsum(vec<vec<Lit>> &newCls, vec<CRef> &refClauses);

  vec<int> tmpVector;
  int computeAdditionalNumberOfClauses(vec<Lit> &orGate);
  void extractEquivClass(vec<vec<Lit>> &equivList, vec<Lit> &equivClass);
  void replaceEquiv(vec<vec<Lit>> &gates);
  void replaceVarByOrGate(vec<Lit> &g);
  void replaceLitByTerm(Lit l, vec<Lit> &lits);
  void replaceLitByClause(Lit l, vec<Lit> &lits);

  void vivifiedSetOfClauses(vec<CRef> &refClauses);
  void occurrenceElimination(Lit l, vec<CRef> &refClauses);
  void constructWatchList(vec<vec<Lit>> &newCls);
  void searchAndRemoveOcc(vec<int> &setOfIdx, int idx);

  inline void showOccurrenceList() {
    for (int i = 0; i < solver.nVars(); i++) {
      if (!markedOutputVars[i])
        continue;
      Lit l = mkLit(i, true);

      printf("%d: ", readableLit(l));
      showListInt(occurrences[toInt(l)]);
      printf("%d: ", readableLit(~l));
      showListInt(occurrences[toInt(~l)]);
    }
  }

  inline void debug() {
    printf("DEBUG FUNCTION\n");

    for (int i = 0; i < solver.clauses.size(); i++) {
      Clause &c = solver.ca[solver.clauses[i]];
      printf("debug %d: ", c.attached());
      showClause(c);
      if (!c.attached())
        continue;

      for (int j = 0; j < c.size(); j++) {
        if (!markedOutputVars[var(c[j])])
          continue;

        vec<int> &v = occurrences[toInt(c[j])];
        bool in = false;
        for (int k = 0; !in && k < v.size(); k++)
          in = v[k] == i;
        assert(in);
      }
    }

    for (int i = 0; i < solver.nVars(); i++) {
      if (!markedOutputVars[i])
        continue;
      Lit l = mkLit(i, false);

      for (int j = 0; j < occurrences[toInt(l)].size(); j++) {
        Clause &c = solver.ca[solver.clauses[occurrences[toInt(l)][j]]];

        printf("&&& %d: ", readableLit(l));
        showClause(c);
        assert(c.attached());

        bool in = false;
        for (int k = 0; !in && k < c.size(); k++)
          in = c[k] == l;
        assert(in);
      }

      l = ~l;
      for (int j = 0; j < occurrences[toInt(l)].size(); j++) {
        Clause &c = solver.ca[solver.clauses[occurrences[toInt(l)][j]]];
        printf("&&& %d: ", readableLit(l));
        showClause(c);
        assert(c.attached());

        bool in = false;
        for (int k = 0; !in && k < c.size(); k++)
          in = c[k] == l;
        assert(in);
      }
    }
  } // debug

  inline void killUnsat() {
    printf("c We detected that the problem is unsat during the forgetting "
           "process\ns UNSATISFIABLE\n");
    exit(20);
  }

  inline uint64_t hashClause(Clause &c) {
    uint64_t ret = 0;
    for (int i = 0; i < c.size(); i++)
      ret |= 1 << (toInt(c[i]) & 63); // = % 64
    return ret;
  }

  inline uint64_t hashSetOfLit(vec<Lit> &c) {
    uint64_t ret = 0;
    for (int i = 0; i < c.size(); i++)
      ret |= 1 << (toInt(c[i]) & 63); // = % 64
    return ret;
  }

  inline void printOccList() {
    printf("--------------------------\n");
    for (int i = 0; i < occurrences.size(); i++) {
      printf("%d => ", readableLit(mkLit(i >> 1, i & 1)));
      showListInt(occurrences[i]);
    }
  } // printOccList

  inline void extractEquivFromGates(vec<vec<Lit>> &gates,
                                    vec<vec<Lit>> &equivList) {
    int i, j;
    for (i = j = 0; i < gates.size(); i++) {
      if (gates[i].size() > 2 && i == j)
        j++;
      else if (gates[i].size() > 2 && i != j) {
        gates[i].copyTo(gates[j++]);
        gates[i].clear();
      } else {
        equivList.push();
        gates[i].copyTo(equivList.last());
      }
    }

    gates.shrink(i - j);
  } // extractEquivFromGates

  inline Var selectVarAndPop(vec<Var> &outputVars) {
    int best = 0,
        score = occurrences[toInt(mkLit(outputVars[0], false))].size() *
                occurrences[toInt(mkLit(outputVars[0], true))].size();

    for (int i = 1; i < outputVars.size(); i++) {
      if (solver.value(outputVars[i]) != l_Undef)
        continue;

      Lit l = mkLit(outputVars[i], false);
      if (!occurrences[toInt(l)].size() || !occurrences[toInt(~l)].size()) {
        best = i;
        break;
      }

      int tmp = occurrences[toInt(l)].size() * occurrences[toInt(~l)].size();
      if (tmp < score) {
        score = tmp;
        best = i;
      }
    }

    Var tmp = outputVars[best];
    outputVars[best] = outputVars.last();
    outputVars.pop();
    return tmp;
  } // selectVarFromPos

  inline void sortClause(Clause &c) {
    vec<Lit> tmp;
    for (int k = 0; k < c.size(); k++)
      tmp.push(c[k]);
    sort(tmp, LitOrderLt(solver.activity, markedOutputVars));
    for (int k = 0; k < c.size(); k++)
      c[k] = tmp[k];
  } // sortClause

  inline void tryGateElimination(Lit lp, GatesDetection &gd) {
    vec<Lit> pg, ng;
    gd.searchOrGateFromLit(solver, pg, lp, occurrences);
    gd.searchOrGateFromLit(solver, ng, ~lp, occurrences);

    /* printf("1) "); showListLit(pg); */
    /* printf("2) "); showListLit(ng); */

    int lim = freePositionInClauses.size();
    if (pg.size() && !ng.size()) {
      if (computeAdditionalNumberOfClauses(pg) <= lim)
        replaceVarByOrGate(pg);
    } else if (ng.size() && !pg.size()) {
      if (computeAdditionalNumberOfClauses(ng) <= lim)
        replaceVarByOrGate(ng);
    }
    if (ng.size() && pg.size()) {
      int nb = computeAdditionalNumberOfClauses(ng),
          pb = computeAdditionalNumberOfClauses(pg);
      if (nb <= lim || pb <= lim) {
        if (nb < pb)
          replaceVarByOrGate(ng);
        else
          replaceVarByOrGate(pg);
      }
    }
  } // tryGateElimination

public:
  Forgetting(Solver &s) : solver(s) {
    timeOccRm = nbRemovedLitOccRm = timeVivi = nbRemovedClauseVivi =
        nbRemovedLitVivi = 0;
    markedLit.initialize(s.nVars() << 1, false);
    stamp = 0;
    for (int i = 0; i < solver.nVars(); i++) {
      markedAsForget.push(false);
      watchNewCls.push();
      watchNewCls.push();
      tmpVector.push(0);
    }
  }

  int runForgetting(vec<Var> &outputVars, vec<Var> &forgetVar, int lim_occ,
                    vec<vec<Lit>> &gates, bool useGate);
};
} // namespace Glucose

#endif
