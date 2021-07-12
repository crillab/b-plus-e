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

#include "core/Forgetting.h"
#include "core/GatesDetection.h"
#include "core/Solver.h"
#include "core/SolverTypes.h"
#include "mtl/Alg.h"
#include "mtl/Heap.h"
#include "mtl/Vec.h"
#include "utils/System.h"

using namespace std;
using namespace Glucose;

/**
   Remove a clause and uptdate the occurrences.

   @param[in] idx, the index of the clause
   @param[in] refClauses, the set of clauses
 */
void Forgetting::removeClauseOcc(int idx, vec<CRef> &refClauses) {
  Clause &c = (solver.ca)[refClauses[idx]];
  if (c.attached())
    solver.detachClause(refClauses[idx], true);

  for (int i = 0; i < c.size(); i++) {
    if (!markedOutputVars[var(c[i])])
      continue;

    // printf("search %d in %d: ", idx, readableLit(c[i]));
    // showListInt(occurrences[toInt(c[i])]);
    searchAndRemoveOcc(occurrences[toInt(c[i])], idx);
  }

  hashKeyInit[idx] = 0;
  freePositionInClauses.push(idx);
  c.mark(1);
  (solver.ca).free(refClauses[idx]);
} // removeClauseOcc

/**
   Add a clause and uptdate the occurrence list.

   @param[in] lits, the clause which is added
   @param[in] refClauses, the set of clauses
 */
void Forgetting::addClauseOcc(vec<Lit> &lits, vec<CRef> &refClauses) {
  assert(lits.size());

  if (lits.size() == 1) {
    if (solver.value(lits[0]) == l_False)
      killUnsat();
    if (solver.value(lits[0]) == l_Undef)
      solver.uncheckedEnqueue(lits[0]);
    assert(solver.value(lits[0]) == l_True);
  } else {
    int pos = (freePositionInClauses.size()) ? freePositionInClauses.last()
                                             : refClauses.size();
    if (pos < refClauses.size())
      freePositionInClauses.pop();
    else {
      refClauses.push();
      hashKeyInit.push();
      stampSubsum.push(0);
    }

    //  printf("addClauseOcc (%d): ", pos); showListLit(lits);

    refClauses[pos] = (solver.ca).alloc(lits, false);
    hashKeyInit[pos] = hashClause((solver.ca)[refClauses[pos]]);
    for (int i = 0; i < lits.size(); i++) {
      if (markedOutputVars[var(lits[i])]) {
        // printf("add %d =< %d\n", readableLit(lits[i]), pos);
        occurrences[toInt(lits[i])].push(pos);
      }
    }

    solver.attachClause(refClauses[pos]);
    solver.ca[refClauses[pos]].markIdx(pos);
  }
} // addClauseOcc

/**
   Initialize the occurrence list with the set of clauses given in
   parameter.

   @param[in] refClauses, the set of reference on clauses
 */
void Forgetting::initOccList(vec<CRef> &refClauses) {
  occurrences.clear();
  for (int i = 0; i < solver.nVars(); i++) {
    // for both phases of a variable (use toInt)
    occurrences.push();
    occurrences.push();
  }

  for (int i = 0; i < refClauses.size(); i++) {
    Clause &c = (solver.ca)[refClauses[i]];

    for (int j = 0; j < c.size(); j++)
      if (markedOutputVars[var(c[j])])
        occurrences[toInt(c[j])].push(i);
  }
} // initOccList

/**
   Try to remove a maximum number of the occurrences clauses of the
   literal l given in parameter.

   @param[in] l, the literal we want to remove
   @param[in] refClauses, the set of clause
 */
void Forgetting::occurrenceElimination(Lit l, vec<CRef> &refClauses) {
  assert(!(solver.learnts).size());
  double currTime = cpuTime();

  // the clause index
  vec<int> v;
  occurrences[toInt(l)].copyTo(v);

  for (int i = 0; i < v.size() && solver.value(l) == l_Undef; i++) {
    CRef &cr = refClauses[v[i]];
    Clause &c = solver.ca[cr];

    solver.newDecisionLevel();

    // we create an 'assumption'
    bool isSAT = false;
    for (int j = 0; j < c.size() && !isSAT; j++) {
      isSAT = solver.value(c[j]) == l_True;
      if (solver.value(c[j]) != l_Undef)
        continue;
      else
        solver.uncheckedEnqueue(c[j] == l ? c[j] : ~c[j]);
    }

    if (isSAT)
      removeClauseOcc(v[i],
                      refClauses); // we can remove the (satisfiable) clause
    else if (solver.propagate() != CRef_Undef) {
      nbRemovedLitOccRm++;
      solver.detachClause(cr, true);

      for (int j = 0; j < c.size(); j++)
        if (c[j] == l) {
          c[j] = c[0];
          c[0] = l;
          break;
        } // push at the front

      if (c.size() > 2) {
        searchAndRemoveOcc(occurrences[toInt(c[0])], v[i]);
        c[0] = c.last();
        c.shrink(1); // remove it
        solver.attachClause(cr);
        hashKeyInit[v[i]] = hashClause(c);
      } else {
        solver.cancelUntil(0);
        if (solver.value(c[1]) == l_Undef)
          solver.uncheckedEnqueue(c[1]);
        removeClauseOcc(v[i], refClauses);
      }
    }

    solver.cancelUntil(0);
  }

  timeOccRm += cpuTime() - currTime;
} // occurrenceElimination

/**
   Realized the vivication [Piette2008] procedure on a set of clauses
   given in parameter.

   WARNING: this function does not work if the set of clauses is not contiguous.

   [Piette2008] Cédric Piette, Youssef Hamadi, Lakhdar Sais:
   Vivifying Propositional Clausal Formulae. ECAI 2008: 525-529
 */
void Forgetting::vivifiedSetOfClauses(vec<CRef> &refClauses) {
  assert(!(solver.learnts).size());

  double currTime = cpuTime();
  for (int i = 0; i < refClauses.size(); i++) {
    CRef &cr = refClauses[i];
    Clause &c = solver.ca[cr];

    if (!c.attached())
      continue;

    solver.newDecisionLevel();
    solver.detachClause(cr, true);
    sortClause(c);

    bool keepClause = true, shorted = false;
    for (int k = 0; k < c.size(); k++) {
      if (solver.value(c[k]) == l_True) {
        keepClause = false;
        break;
      }
      if (solver.value(c[k]) == l_False) {
        if (markedOutputVars[var(c[k])])
          searchAndRemoveOcc(occurrences[toInt(c[k])], i);

        nbRemovedLitVivi++;
        c[k--] = c[c.size() - 1];
        c.shrink(1);
        shorted = true;
        continue;
      }

      solver.uncheckedEnqueue(~c[k]);
      CRef confl = solver.propagate();

      if (confl != CRef_Undef) {
        keepClause = false;
        break;
      }
    }

    solver.cancelUntil(0);
    if (!keepClause || c.size() <= 1) {
      nbRemovedClauseVivi++;
      removeClauseOcc(i, refClauses);
    } else {
      solver.attachClause(cr);
      if (shorted)
        hashKeyInit[i] = hashClause(c);
    }

    if (c.size() == 1 && solver.value(c[0]) == l_Undef)
      solver.uncheckedEnqueue(c[0]);
  }

  vec<bool> mustBeRm;
  mustBeRm.initialize(refClauses.size(), false);
  for (int i = 0; i < freePositionInClauses.size(); i++)
    mustBeRm[freePositionInClauses[i]] = true;
  for (int i = 0; i < refClauses.size(); i++)
    if (!mustBeRm[i])
      assert(solver.ca[refClauses[i]].attached());

  timeVivi += cpuTime() - currTime;
} // vivifiedSetOfClauses

/**
   Construct the list of watch for a set of new clauses (vec< vec<Lit> >).

   @param[out] watchNewCls, the list of watch on the new clauses
   @param[out] newCls, the new clauses
 */
void Forgetting::constructWatchList(vec<vec<Lit>> &newCls) {
  for (int i = 0; i < watchNewCls.size(); i++)
    watchNewCls[i].setSize(0);

  for (int i = 0; i < newCls.size(); i++) {
    // we want to watch the first literal (but we need to change to avoid the
    // collisions
    int pos = i % newCls[i].size();
    Lit tmp = newCls[i][pos];
    newCls[i][pos] = newCls[i][0];
    newCls[i][0] = tmp;

    watchNewCls[toInt(tmp)].push(i);
  }
} // constructWatchList

/**
   Remove the subsumed clauses.

   @param[out] newCls, the new clauses which contains only non subsubmed clauses
   in the end of the process
 */
void Forgetting::removeSubsum(vec<vec<Lit>> &newCls, vec<CRef> &refClauses) {
  // create the hash tables
  vec<uint64_t> hashKeyNew;
  for (int i = 0; i < newCls.size(); i++)
    hashKeyNew.push(hashSetOfLit(newCls[i]));

  constructWatchList(
      newCls); // Construct a watch list for the clauses given in parameter

  for (int i = 0; i < newCls.size(); i++) {
    stamp++;
    vec<Lit> &cnew = newCls[i];
    for (int j = 0; j < cnew.size(); j++)
      markedLit[toInt(cnew[j])] = true;

    bool isSubSum = false;
    for (int j = 0; j < cnew.size() && !isSubSum; j++) {
      // look for the watches for the new clauses
      vec<int> &idxs = watchNewCls[toInt(cnew[j])];
      for (int k = 0; k < idxs.size() && !isSubSum; k++) {
        if (idxs[k] == i ||
            (hashKeyNew[i] & hashKeyNew[idxs[k]]) != hashKeyNew[idxs[k]])
          continue;
        vec<Lit> &cl = newCls[idxs[k]];

        if (cl.size() > cnew.size())
          continue;

        isSubSum = true;
        for (int l = 0; l < cl.size() && isSubSum; l++)
          isSubSum = markedLit[toInt(cl[l])];
      }

      // look for the watches for the init clauses
      vec<Watcher> &wb = solver.watchesBin[~cnew[j]];
      for (int k = 0; k < wb.size() && !isSubSum; k++) {
        Clause &cl = solver.ca[wb[k].cref];
        if (stampSubsum[cl.markIdx()] == stamp)
          continue;
        else
          stampSubsum[cl.markIdx()] = stamp;
        if ((hashKeyNew[i] & hashKeyInit[cl.markIdx()]) !=
            hashKeyInit[cl.markIdx()])
          continue;

        if (cl.size() > cnew.size())
          continue;
        isSubSum = true;
        for (int l = 0; l < cl.size() && isSubSum; l++)
          isSubSum = markedLit[toInt(cl[l])];
      }

      // look for the watches for the init clauses
      vec<Watcher> &ws = solver.watches[~cnew[j]];
      for (int k = 0; k < ws.size() && !isSubSum; k++) {
        Clause &cl = solver.ca[ws[k].cref];
        if (stampSubsum[cl.markIdx()] == stamp)
          continue;
        else
          stampSubsum[cl.markIdx()] = stamp;
        if ((hashKeyNew[i] & hashKeyInit[cl.markIdx()]) !=
            hashKeyInit[cl.markIdx()])
          continue;

        if (cl.size() > cnew.size())
          continue;
        isSubSum = true;
        for (int l = 0; l < cl.size() && isSubSum; l++)
          isSubSum = markedLit[toInt(cl[l])];
      }
    }

    for (int j = 0; j < cnew.size(); j++)
      markedLit[toInt(cnew[j])] = false;

    if (isSubSum) // this clause is useless
    {
      searchAndRemoveOcc(watchNewCls[toInt(cnew[0])], i);
      cnew.clear();
    }
  }

  int i, j;
  for (i = j = 0; i < newCls.size(); i++)
    if (newCls[i].size())
      if (i != j)
        newCls[i].copyTo(newCls[j++]);
      else
        j++;
  newCls.shrink(i - j);
} // removeSubsum

/**
   From a given variable, the set of resolution obtained from a set of
   clauses is generated and returned.

   @param[in] v, the variable which is used as pivot
   @param[out] cls, the result of the operation
   @param[in] refClauses, the set of clauses

   \return false if the the number of clauses generated is greater
   than limitNbRes, true otherwise
 */
void Forgetting::generateAllResolution(Var v, vec<vec<Lit>> &cls,
                                       vec<CRef> &refClauses) {
  for (int i = 0; i < markedLit.size(); i++)
    assert(!markedLit[i]);

  Lit lPos = mkLit(v, false), lNeg = ~lPos;

  vec<int> &idxPosLit = occurrences[toInt(lPos)];
  vec<int> &idxNegLit = occurrences[toInt(lNeg)];

  for (int i = 0; i < idxPosLit.size(); i++) {
    Clause &cp = (solver.ca)[refClauses[idxPosLit[i]]];

    vec<Lit> base;
    for (int j = 0; j < cp.size(); j++) {
      markedLit[toInt(cp[j])] = true;
      if (cp[j] != lPos && solver.value(cp[j]) != l_False)
        base.push(cp[j]);
    }

    for (int j = 0; j < idxNegLit.size(); j++) {
      vec<Lit> currCl;
      bool taut = false;

      Clause &cn = (solver.ca)[refClauses[idxNegLit[j]]];
      base.copyTo(currCl);

      // resolution
      for (int k = 0; k < cn.size() && !taut; k++) {
        if (cn[k] == lNeg || solver.value(cn[k]) == l_False)
          continue;
        taut = markedLit[toInt(~cn[k])] || solver.value(cn[k]) == l_True;

        if (!markedLit[toInt(cn[k])])
          currCl.push(cn[k]);
      }

      if (!taut) {
        cls.push();
        currCl.copyTo(cls.last());
      }
    }

    for (int j = 0; j < cp.size(); j++)
      markedLit[toInt(cp[j])] = false;
  }
} // generateAllResolution

/**
   Search in a given list if an element occurs or not. In the positive
   case this element is removed.

   @param[out] setOfIdx, the set of idx where we search
   @param[in] idx, the element we search to remove
 */
void Forgetting::searchAndRemoveOcc(vec<int> &setOfIdx, int idx) {
  int pos = -1;
  for (int j = 0; j < setOfIdx.size() && pos == -1; j++)
    if (setOfIdx[j] == idx)
      pos = j;

  assert(pos != -1);
  setOfIdx[pos] = setOfIdx.last();
  setOfIdx.pop();
} // searchAndRemoveOcc

/**
   From a set of given equivalences, we compute the equivalence class.

   @param[in] equivList, the equivalence list
   @param[out] equivClass, the equivalence class computed
*/
void Forgetting::extractEquivClass(vec<vec<Lit>> &equivList,
                                   vec<Lit> &equivClass) {
  vec<int> stampChain;
  equivClass.clear();
  for (int i = 0; i < solver.nVars(); i++) {
    equivClass.push(mkLit(i, false));
    stampChain.push(0);
  }

  int stampChainIdx = 0;
  for (int i = 0; i < equivList.size(); i++) {
    if (!equivList[i].size())
      continue;

    stampChainIdx++;
    stampChain[var(equivList[i][0])] = stampChainIdx;

    vec<Var> chain;
    Var varInput = markedOutputVars[var(equivList[i][0])]
                       ? var_Undef
                       : var(equivList[i][0]);
    chain.push(var(equivList[i][0]));

    bool findAtLeastOn = true;
    while (findAtLeastOn) {
      findAtLeastOn = false;

      for (int j = i; j < equivList.size(); j++) {
        if (!equivList[j].size())
          continue;
        if (stampChain[var(equivList[j][0])] ==
            stampChain[var(equivList[j][1])]) // already/not renamed
        {
          if (stampChain[var(equivList[j][0])] == stampChainIdx)
            equivList[j].clear();
          continue;
        }

        Lit lStamp = lit_Undef, lNoStamp = lit_Undef;
        if (stampChain[var(equivList[j][0])] != stampChainIdx)
          lNoStamp = equivList[j][0];
        else
          lStamp = equivList[j][0];
        if (stampChain[var(equivList[j][1])] != stampChainIdx)
          lNoStamp = equivList[j][1];
        else
          lStamp = equivList[j][1];
        assert(lStamp != lit_Undef && lNoStamp != lit_Undef);

        if (sign(lStamp)) {
          lStamp = ~lStamp;
          lNoStamp = ~lNoStamp;
        } // adjust the sign
        if (sign(lNoStamp))
          equivClass[var(lNoStamp)] = ~equivClass[var(lStamp)];
        else
          equivClass[var(lNoStamp)] = equivClass[var(lStamp)];

        // keep the input variable if it exists
        chain.push(var(lNoStamp));
        if (varInput == var_Undef)
          varInput =
              markedOutputVars[var(lNoStamp)] ? var_Undef : var(lNoStamp);

        findAtLeastOn = true;
        stampChain[var(equivList[j][0])] = stampChain[var(equivList[j][1])] =
            stampChainIdx;
        equivList[j].clear();
      }
    }

    // adjust if an input have been found
    if (varInput != var_Undef) {
      Lit pos = mkLit(varInput, sign(equivClass[varInput]));
      for (int i = 0; i < chain.size(); i++)
        if (sign(equivClass[chain[i]]))
          equivClass[chain[i]] = ~pos;
        else
          equivClass[chain[i]] = pos;
    }
  }
} // extractEquivClass

/**
   Firstly, we replace the equivalence present in the vector gates
   given in parameter.

   @param[in] gates, a set of gates
 */
void Forgetting::replaceEquiv(vec<vec<Lit>> &gates) {
  vec<Lit> equivClass;

  // collect the equivalences class
  vec<vec<Lit>> equivList;
  extractEquivFromGates(gates, equivList);
  printf("c The number of equivalences detected is: %d\n", equivList.size());
  extractEquivClass(equivList, equivClass);

  // make the replacement
  vec<CRef> &clauses = solver.clauses;
  for (int i = 0; i < clauses.size(); i++)
    solver.detachClause(clauses[i], true);

  int i, j;
  for (i = j = 0; i < clauses.size(); i++) {
    Clause &c = solver.ca[clauses[i]];

    vec<Lit> ps;
    int change = false;
    for (int k = 0; k < c.size(); k++) {
      if (markedOutputVars[var(c[k])] &&
          var(equivClass[var(c[k])]) != var(c[k])) {
        change = true;
        if (sign(c[k]))
          c[k] = ~equivClass[var(c[k])];
        else
          c[k] = equivClass[var(c[k])];
      }
      ps.push(c[k]);
    }
    if (!change) {
      clauses[j++] = clauses[i];
      continue;
    }

    sort(ps);
    bool isSAT = false;
    int ki = 0, kj = 0;

    for (Lit p = lit_Undef; !isSAT && ki < ps.size(); ki++) {
      isSAT = (solver.value(ps[ki]) == l_True || ps[ki] == ~p);
      if (solver.value(ps[ki]) != l_False && ps[ki] != p)
        ps[kj++] = p = ps[ki];
    }
    ps.shrink(ki - kj);

    if (isSAT) {
      c.mark(1);
      (solver.ca).free(clauses[i]);
    } else if (ps.size() == 0)
      killUnsat();
    else if (ps.size() == 1) {
      isSAT = true;
      if (solver.value(ps[0]) == l_False)
        killUnsat();
      if (solver.value(ps[0]) == l_Undef)
        solver.uncheckedEnqueue(ps[0]);
    } else {
      for (int k = 0; k < ps.size(); k++)
        c[k] = ps[k];

      c.shrink(c.size() - ps.size());
      clauses[j++] = clauses[i];
    }
  }
  clauses.shrink(i - j);
  printf("c The number of clauses removed during the equivalence process: %d\n",
         i - j);
  for (int i = 0; i < clauses.size(); i++)
    solver.attachClause(clauses[i]);
} // replaceEquiv

/**
   Compute the number of additional literals after or gate
   replacement
   @param[in] g, the gate
   \return the number of additional literals
*/
int Forgetting::computeAdditionalNumberOfClauses(vec<Lit> &orGate) {
  int ret = 0;
  Lit l = orGate[0];

  for (int i = 1; i < orGate.size(); i++)
    markedLit[var(orGate[i])] = sign(orGate[i]) + 1;

  // printf("computeAdditionalNumberOfClauses: ");  showListLit(orGate);

  vec<int> &v1 = occurrences[toInt(l)];
  for (int i = 0; i < v1.size(); i++) {
    Clause &c = solver.ca[solver.clauses[v1[i]]];
    // printf("+ "); showClause(c);
    ret++;
    for (int j = 0; j < c.size(); j++)
      if (markedLit[var(c[j])] + sign(c[j]) == 2) {
        ret--;
        break;
      }
  }
  // printf("+ ret = %d\n", ret);

  // ret = 0;

  vec<int> &v2 = occurrences[toInt(~l)];
  for (int i = 1; i < orGate.size(); i++)
    markedLit[var(orGate[i])] = sign(~orGate[i]) + 1;
  for (int i = 0; i < v2.size(); i++) {
    Clause &c = solver.ca[solver.clauses[v2[i]]];
    // printf("- "); showClause(c);
    int cpt = orGate.size() - 1;

    for (int j = 0; j < c.size(); j++) {
      if ((markedLit[var(c[j])] + sign(c[j])) == 2)
        cpt--;
      if (markedLit[var(c[j])] && ((markedLit[var(c[j])] + sign(c[j])) & 1)) {
        cpt = 1;
        break;
      }
    }

    ret += cpt;
  }
  // printf("- ret = %d\n", ret);

  // printf("ret = %d\n", ret - v1.size() - v2.size());

  for (int i = 1; i < orGate.size(); i++)
    markedLit[var(orGate[i])] = 0;
  return ret - v1.size() - v2.size();
} // computeAdditionalNumberOfClause

/**
   Replace in all clauses a given literal by a term.

   @param[in] l, the literal
   @param[in] lits, the term
 */
void Forgetting::replaceLitByTerm(Lit l, vec<Lit> &lits) {
  vec<int> nv;
  occurrences[toInt(l)].copyTo(nv);
  for (int i = 0; i < lits.size(); i++)
    markedLit[var(lits[i])] = 1 + sign(lits[i]);

  for (int i = 0; i < nv.size(); i++) {
    CRef cr = solver.clauses[nv[i]];
    Clause &c = solver.ca[cr];
    // printf("Init: "); showClause(c);

    vec<Lit> addClause;
    bool subsum = false;
    for (int j = 0; j < c.size(); j++) {
      if (c[j] != l)
        addClause.push(c[j]);
      if (markedLit[var(c[j])])
        markedLit[var(c[j])] += 1 + sign(c[j]);

      // printf("==> %d = %d\n", readableLit(c[j]), markedLit[var(c[j])]);
      subsum = subsum ||
               (markedLit[var(c[j])] &&
                !(markedLit[var(c[j])] & 1)); // markedLit[var(c[j])] == 2 || 4
    }

    if (subsum) {
      // printf("subsum\n");

      if (addClause.size() > 1) {
        solver.clauses[nv[i]] = (solver.ca).alloc(addClause, false);
        solver.attachClause(solver.clauses[nv[i]]);
        hashKeyInit[nv[i]] = hashSetOfLit(addClause);
      } else {
        removeClauseOcc(nv[i], solver.clauses);
        if (solver.value(addClause[0]) == l_Undef)
          solver.uncheckedEnqueue(addClause[0]);
      }

      c.mark(1);
      (solver.ca).free(cr);
    } else {
      removeClauseOcc(nv[i], solver.clauses);

      for (int j = 0; j < lits.size(); j++) {
        // printf("booo %d : %d\n", markedLit[var(lits[j])],
        // readableLit(lits[j]));
        if (markedLit[var(lits[j])] != 3) {
          addClause.push(lits[j]);
          addClauseOcc(addClause, solver.clauses);
          // printf("add: "); showListLit(addClause);
          addClause.pop();
        }
      }
    }

    for (int j = 0; j < lits.size(); j++)
      markedLit[var(lits[j])] = 1 + sign(lits[j]);
    // printf("reinit\n");
    // for(int j = 0 ; j<lits.size() ; j++) printf("%d ~~> %d\n",
    // readableLit(lits[j]), markedLit[var(lits[j])]);
  }

  // unmark term
  for (int i = 0; i < lits.size(); i++)
    markedLit[var(lits[i])] = 0;
  occurrences[toInt(l)].clear();
} // replaceLitByTerm

/**
   Replace in all clauses a given literal by a clause.

   @param[in] l, the literal
   @param[in] lits, the clause
*/
void Forgetting::replaceLitByClause(Lit l, vec<Lit> &lits) {
  int initSize = lits.size();
  for (int i = 0; i < lits.size(); i++)
    markedLit[var(lits[i])] = sign(lits[i]) + 1;
  assert(markedOutputVars[var(l)]);

  vec<int> pv;
  occurrences[toInt(l)].copyTo(pv);

  for (int i = 0; i < pv.size(); i++) {
    CRef cr = solver.clauses[pv[i]];
    for (int k = 0; k < lits.size(); k++)
      assert(markedLit[var(lits[k])] == sign(lits[k]) + 1);

    assert(solver.ca[cr].attached());
    solver.detachClause(cr, true);

    Clause &c = solver.ca[cr];
    bool taut = false;

    for (int j = 0, end = c.size(); !taut && j < end; j++) {
      if (solver.value(c[j]) == l_False)
        continue;

      if (c[j] == l)
        continue;
      else if (!markedLit[var(c[j])])
        lits.push(c[j]);
      else {
        taut = (markedLit[var(c[j])] + sign(c[j]) == 2) ||
               solver.value(c[j]) == l_True;
        markedLit[var(c[j])] += 3;
      }
    }

    assert(lits.size() || taut); // /!\ lits.size() > 0 ==> SAT!!!

    if (!taut && lits.size() > 1) {
      // printf("NOT TAUT %d: ", pv[i]); showClause(c);
      solver.clauses[pv[i]] = (solver.ca).alloc(lits, false);
      hashKeyInit[pv[i]] = hashSetOfLit(lits);
      lits.shrink(lits.size() - initSize);

      // update the occurence list
      for (int j = 0; j < lits.size(); j++)
        if (markedOutputVars[var(lits[j])] && markedLit[var(lits[j])] <= 3)
          occurrences[toInt(lits[j])].push(pv[i]);
      solver.attachClause(solver.clauses[pv[i]]);
    } else {
      // printf("MUST BE REMOVED %d\n", pv[i]);

      if (!taut && lits.size() == 1 && solver.value(lits[i]) == l_Undef)
        solver.uncheckedEnqueue(lits[0]);

      for (int j = 0; j < c.size(); j++)
        if (c[j] != l && markedOutputVars[var(c[j])])
          searchAndRemoveOcc(occurrences[toInt(c[j])], pv[i]);

      hashKeyInit[pv[i]] = 0;
      freePositionInClauses.push(pv[i]);

      lits.shrink(lits.size() - initSize);
    }

    for (int j = 0; j < lits.size(); j++)
      markedLit[var(lits[j])] = sign(lits[j]) + 1;

    (solver.ca[cr]).mark(1);
    (solver.ca).free(cr);
  }

  for (int i = 0; i < lits.size(); i++)
    markedLit[var(lits[i])] = 0;
  occurrences[toInt(l)].clear();
} // replaceLitByClause

/**
   Replace a variable by its definition and update all the structures.

   @param[in] g, the gate
 */
void Forgetting::replaceVarByOrGate(vec<Lit> &g) {
  vec<Lit> lits;
  for (int i = 1; i < g.size(); i++)
    lits.push(g[i]);

  // printf("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~> replaceVarByOrGate: ");
  // showListLit(g); debug(); printf("------------------\n");

  // printf("#################################################\n");
  // showOccurrenceList();

  // first, we replace the positive literal
  Lit l = g[0];
  replaceLitByClause(l, lits);

  // printf("++++++++++++++++++++++++++++++++++++++++++++++++\n");
  // showOccurrenceList();

  // then, we replace the negative literal
  for (int i = 0; i < lits.size(); i++)
    lits[i] = ~lits[i];
  replaceLitByTerm(~l, lits);

  // printf("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");
  // showOccurrenceList();

  // debug();
  // printf("END\n");
  // exit(0);
} // replaceVarByOrGate

/**
   Realize the forgetting on a set of variables given in parameter.

   @param[in] outputVars, the set of variables we want to forget
   @param[out] forgetVars, the set of variables forget

   \return the number of variable removed during all the process
 */
int Forgetting::runForgetting(vec<Var> &outputVars, vec<Var> &forgetVars,
                              int lim_occ, vec<vec<Lit>> &gates,
                              bool useGates) {
  GatesDetection gd(solver);

  for (int i = 0; i < solver.learnts.size(); i++)
    solver.removeClause((solver.learnts)[i], true);
  (solver.learnts).clear();

  double initTime = cpuTime();
  int nbIteration = 0;

  markedOutputVars.initialize(solver.nVars(), false);
  // printf("O = ");
  for (int i = 0; i < outputVars.size(); i++) {
    // printf("%d ", outputVars[i] + 1);
    markedOutputVars[outputVars[i]] = true;
  }
  // printf("\n");

  if (useGates) {
    replaceEquiv(gates);
    printf("c The number of OR gates is: %d\n", gates.size());
  }

  vec<CRef> &refClauses = solver.clauses;
  for (int i = 0; i < refClauses.size(); i++) {
    hashKeyInit.push(hashClause(solver.ca[refClauses[i]]));
    solver.ca[refClauses[i]].markIdx(i);
    stampSubsum.push(0);
  }

  // we create the occurence list refer all the clause where an output variable
  // exist
  initOccList(refClauses);
  vivifiedSetOfClauses(refClauses);

  bool forgetApplied = true;
  while (forgetApplied) {
    nbIteration++;
    forgetApplied = false;
    vec<Var> notAlreadyForget;

    // apply the forgetting on all the variables of outputVars
    while (outputVars.size()) {
      // debug();

      Var varSelected = selectVarAndPop(outputVars);
      // printf("~~~~~~~  %d  ~~~~~~~~~~\n", varSelected + 1);
      if (solver.value(varSelected) != l_Undef)
        continue;

      Lit lp = mkLit(varSelected, false);
      // occurrenceElimination(lp, refClauses);
      // occurrenceElimination(~lp, refClauses);

      // gate option
      if (useGates)
        tryGateElimination(lp, gd);

      if (occurrences[toInt(lp)].size() * occurrences[toInt(~lp)].size() >
          lim_occ) {
        notAlreadyForget.push(varSelected);
        continue;
      }

      vec<vec<Lit>> genResolution;
      generateAllResolution(varSelected, genResolution, refClauses);
      removeSubsum(genResolution, refClauses);

      int sureRm =
          occurrences[toInt(lp)].size() + occurrences[toInt(~lp)].size();
      if (genResolution.size() <= sureRm) {
        markedAsForget[varSelected] = true;
        forgetVars.push(varSelected);

        forgetApplied = true;
        vec<int> idxRm;
        for (int j = 0; j < occurrences[toInt(lp)].size(); j++)
          idxRm.push(occurrences[toInt(lp)][j]);
        for (int j = 0; j < occurrences[toInt(~lp)].size(); j++)
          idxRm.push(occurrences[toInt(~lp)][j]);

        for (int j = 0; j < idxRm.size(); j++)
          removeClauseOcc(idxRm[j], refClauses);
        for (int j = 0; j < genResolution.size(); j++)
          addClauseOcc(genResolution[j], refClauses);
      } else
        notAlreadyForget.push(varSelected);
    }

    vivifiedSetOfClauses(refClauses);
    notAlreadyForget.copyTo(outputVars);
  }

  // shrink
  vec<bool> mustBeRm;
  mustBeRm.initialize(refClauses.size(), false);
  for (int i = 0; i < freePositionInClauses.size(); i++)
    mustBeRm[freePositionInClauses[i]] = true;

  int i, j;
  for (i = j = 0; i < refClauses.size(); i++)
    if (!mustBeRm[i])
      refClauses[j++] = refClauses[i];
  refClauses.shrink(i - j);

  printf("c Number of variables forgotten: %d\n", forgetVars.size());
  printf("c Number of iterations: %d\n", nbIteration);
  printf("c\nc Vivification, total time: %lf\n", timeVivi);
  printf("c Vivification, number of clauses removed: %d\n",
         nbRemovedClauseVivi);
  printf("c Vivification, number of literals removed: %d\n", nbRemovedLitVivi);
  printf("c\nc Occurrence Elimination, total time: %lf\n", timeOccRm);
  printf("c Occurrence Elimination, number of literals removed: %d\n",
         nbRemovedLitOccRm);

  printf("c Time used for the preprocessing step: %lf\nc\n",
         cpuTime() - initTime);

  // exit(0);
  return forgetVars.size();
} // runForgetting
