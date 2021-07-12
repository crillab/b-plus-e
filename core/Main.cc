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
/*****************************************************************************************[Main.cc]
 Glucose -- Copyright (c) 2009, Gilles Audemard, Laurent Simon
                                CRIL - Univ. Artois, France
                                LRI  - Univ. Paris Sud, France

Glucose sources are based on MiniSat (see below MiniSat copyrights). Permissions
and copyrights of Glucose are exactly the same as Minisat on which it is based
on. (see below).

---------------

Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>

#include <signal.h>
#include <zlib.h>

#include "core/Backbone.h"
#include "core/DefinableDetection.h"
#include "core/Dimacs.h"
#include "core/Forgetting.h"
#include "core/GatesDetection.h"
#include "core/Solver.h"
#include "utils/Options.h"
#include "utils/ParseUtils.h"
#include "utils/System.h"

using namespace Glucose;

void printStats(Solver &solver) {
  double cpu_time = cpuTime();
  printf("c restarts              : %" PRIu64 " (%" PRIu64
         " conflicts in avg)\n",
         solver.starts,
         (solver.starts > 0 ? solver.conflicts / solver.starts : 0));
  printf("c blocked restarts      : %" PRIu64 " (multiple: %" PRIu64 ") \n",
         solver.nbstopsrestarts, solver.nbstopsrestartssame);
  printf("c last block at restart : %" PRIu64 "\n", solver.lastblockatrestart);
  printf("c nb ReduceDB           : %ld\n", solver.nbReduceDB);
  printf("c nb removed Clauses    : %ld\n", solver.nbRemovedClauses);
  printf("c nb learnts DL2        : %ld\n", solver.nbDL2);
  printf("c nb learnts size 2     : %ld\n", solver.nbBin);
  printf("c nb learnts size 1     : %ld\n", solver.nbUn);
  printf("c conflicts             : %-12" PRIu64 "   (%.0f /sec)\n",
         solver.conflicts, solver.conflicts / cpu_time);
  printf("c decisions             : %-12" PRIu64
         "   (%4.2f %% random) (%.0f /sec)\n",
         solver.decisions,
         (float)solver.rnd_decisions * 100 / (float)solver.decisions,
         solver.decisions / cpu_time);
  printf("c propagations          : %-12" PRIu64 "   (%.0f /sec)\n",
         solver.propagations, solver.propagations / cpu_time);
  printf("c conflict literals     : %-12" PRIu64 "   (%4.2f %% deleted)\n",
         solver.tot_literals,
         (solver.max_literals - solver.tot_literals) * 100 /
             (double)solver.max_literals);
  printf("c nb reduced Clauses    : %ld\n", solver.nbReducedClauses);

  printf("c CPU time              : %g s\n", cpu_time);
  printf("c\n");
} // printStats

int satOracle(vec<vec<Lit>> &clauses, int nbVar, bool mod, int verb, int vv) {
  Solver S;

  S.verbosity = verb;
  S.verbEveryConflicts = vv;
  S.showModel = mod;

  while (S.nVars() < nbVar)
    S.newVar();
  for (int i = 0; i < clauses.size(); i++)
    S.addClause_(clauses[i]);

  if (S.verbosity > 0) {
    printf("c ========================================[ Problem Statistics "
           "]===========================================\n");
    printf("c |                                                                "
           "                                       |\n");
    printf("c |  Number of variables:  %12d                                    "
           "                               |\n",
           S.nVars());
    printf("c |  Number of clauses:    %12d                                    "
           "                               |\n",
           S.nClauses());
  }

  if (!S.simplify()) {
    if (S.certifiedOutput != NULL)
      fprintf(S.certifiedOutput, "0\n"), fclose(S.certifiedOutput);
    if (S.verbosity > 0) {
      printf("c "
             "================================================================="
             "========================================\n");
      printf("Solved by unit propagation\n");
      printStats(S);
      printf("\n");
    }
    printf("s UNSATISFIABLE\n");
    exit(20);
  }

  vec<Lit> dummy;
  lbool ret = S.solveLimited(dummy);
  if (S.verbosity > 0)
    printStats(S);

  printf(ret == l_True    ? "s SATISFIABLE\n"
         : ret == l_False ? "s UNSATISFIABLE\n"
                          : "s INDETERMINATE\n");
  if (S.showModel && ret == l_True) {
    printf("v ");
    for (int i = 0; i < S.nVars(); i++)
      if (S.model[i] != l_Undef)
        printf("%s%s%d", (i == 0) ? "" : " ", (S.model[i] == l_True) ? "" : "-",
               i + 1);
    printf(" 0\n");
  }

#ifdef NDEBUG
  exit(ret == l_True    ? 10
       : ret == l_False ? 20
                        : 0); // (faster than "return", which will invoke the
                              // destructor for 'Solver')
#else
  return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
} // satOracle

/**
   Rebuilt a set of clauses from a solver.

   @param[in] S, the solver
   @param[out] clauses, the result
 */
void rebuiltClauses(Solver &S, vec<vec<Lit>> &clauses) {
  S.removeSatisfied(S.clauses);

  for (int i = 0; i < clauses.size(); i++)
    clauses[i].clear();
  clauses.clear();
  for (int i = 0; i < (S.clauses).size(); i++) {
    Clause &c = S.ca[S.clauses[i]];
    clauses.push();
    for (int j = 0; j < c.size(); j++)
      if (S.value(c[j]) == l_Undef)
        (clauses.last()).push(c[j]);
  }
  for (int i = 0; i < S.trail.size(); i++) {
    clauses.push();
    (clauses.last()).push(S.trail[i]);
  }
} // rebuiltClauses

void appliedB(vec<vec<Lit>> &clauses, int nbVar, int lim_solver,
              StringOption &definabilitySort, StringOption &outPutFile,
              bool useGates, vec<Var> &protectedVar) {
  Solver S;
  while (S.nVars() < nbVar)
    S.newVar();
  for (int i = 0; i < clauses.size(); i++)
    S.addClause_(clauses[i]);
  if (!S.simplify() || !S.solve()) {
    printf("p cnf %d 2\n1 0\n-1 0\n", nbVar);
    exit(0);
  } // unsat formula

  // the formula is satisfiable
  Backbone bb;
  bb.computeBackBone(S, S.model);

  // collect gates (if option is activated)
  vec<vec<Lit>> gates;
  if (useGates) {
    GatesDetection gd(S);
    gd.collectGates(S, gates, protectedVar);
  }

  // we compute a bi-partition
  rebuiltClauses(S, clauses);

  vec<Var> input, output;
  DefinableDetection fDec;
  fDec.collectBiPartition(clauses, nbVar, input, output, lim_solver,
                          definabilitySort, gates, protectedVar);

  FILE *out = fopen(outPutFile, "a");
  fprintf(out, "v ");
  for (int i = 0; i < input.size(); i++)
    fprintf(out, "%d ", input[i] + 1);
  fprintf(out, "0\n");
} // appliedB

/**
   Realize the E preprocessing.

   @param[in] S, a SAT solver
   @param[in] lim_occ, limit the maximal number of authorized resolution
   @param[in] inPutFile, the name of the file where the variables we want to
   forget are given
 */
void appliedE(vec<vec<Lit>> &clauses, int nbVar, int lim_occ,
              StringOption &inPutFile, bool useGates, vec<Var> &protectedVar) {
  Solver S;
  while (S.nVars() < nbVar)
    S.newVar();
  for (int i = 0; i < clauses.size(); i++)
    S.addClause_(clauses[i]);

  // collect gates (if option is activated)
  vec<vec<Lit>> gates;
  if (useGates) {
    GatesDetection gd(S);
    gd.collectGates(S, gates, protectedVar);
  }

  Forgetting fo(S);

  // collect the variable we have to forget
  vec<Var> outVars, forgetVariables;
  FILE *inFile = fopen(inPutFile, "rb");
  assert(inFile);

  int cNb = 0;
  bool nbInProgress = false;

  int c;
  while ((c = fgetc(inFile)) != 'V' && c != EOF && c != 'v')
    ;
  assert(c == 'V' || c == 'v');

  do {
    c = fgetc(inFile);

    if (c == '\n' || c == ' ' || feof(inFile)) {
      if (nbInProgress && cNb == 0)
        break;
      if (nbInProgress)
        outVars.push(cNb - 1);
      if (feof(inFile))
        break;

      cNb = 0;
      nbInProgress = false;
    } else if (c == 'c') {
      while (c != '\n' && !feof(inFile))
        c = fgetc(inFile);
      nbInProgress = false;
    } else {
      cNb = (cNb * 10) + (c - '0');
      assert(c >= '0' && c <= '9');
      nbInProgress = true;
    }
  } while (1);

  fclose(inFile);

  fo.runForgetting(outVars, forgetVariables, lim_occ, gates, useGates);

  printf("p cnf %d %d\n", S.nVars(),
         S.clauses.size() + S.trail.size() + forgetVariables.size());
  S.showSimplifiedFormula();
} // appliedE

inline void showInstanceAfterPreproc(vec<vec<Lit>> &clauses,
                                     vec<Var> &varRemoved, vec<Lit> &trail,
                                     int initNbVar) {
  int nbLit = 0, gt5 = 0, gt10 = 0, binaryClause = 0;

  if (!clauses.size()) {
    printf("c Solved by preprocessing\n");
    printf("c Information about the instance\n");
    printf("c Number of variables: %d\n", 0);
    printf("c Number of clauses: %d\n", 0);
    printf("c Number of literals: %d\n", 0);
    printf("c Unit literal: %d\n", trail.size());
    printf("c Number of variable forgot: %d\n", varRemoved.size());
    printf("s %.0lf\n", pow(2, initNbVar - varRemoved.size() - trail.size()));
    exit(30); // solve by preproc
  }

  printf("p cnf %d %d\n", initNbVar,
         clauses.size() + trail.size() + varRemoved.size());
  for (int i = 0; i < trail.size(); i++)
    printf("%d 0\n", readableLit(trail[i]));
  for (int i = 0; i < varRemoved.size();
       i++) // arbitrary force the value of deleted variable
  {
    Lit l = mkLit(varRemoved[i], true);
    printf("%d 0\n", readableLit(l));
  }

  for (int i = 0; i < clauses.size(); i++) {
    for (int j = 0; j < clauses[i].size(); j++)
      printf("%d ", readableLit(clauses[i][j]));
    printf("0\n");

    int sz = clauses[i].size();
    if (sz >= 10)
      gt10++;
    else if (sz >= 5)
      gt5++;
    else if (sz == 2)
      binaryClause++;
    nbLit += sz;
  }

  printf("c Information about the instance\n");
  printf("c Number of variables: %d\n", initNbVar);
  printf("c Number of clauses: %d\n", clauses.size());
  printf("c Number of literals: %d\n", nbLit);
  printf("c Clause greater than or equals to 10: %d\n", gt10);
  printf("c Clause between 9 and 5: %d\n", gt5);
  printf("c Number of binary clauses : %d\n", binaryClause);
  printf("c Unit literal: %d\n", trail.size());
  printf("c Number of variable forgot: %d\n", varRemoved.size());
} // showInstanceAfterPreproc

/**
   Realize the B+E preprocessing.

   @param[in] lim_solver, how many conflict for the SAT oracle
   @param[in] definabilitySort, the method used to sort the literal to check the
   definability
   @param[in] lim_occ, limit the maximal number of authorized resolution
 */
void appliedPreproc(vec<vec<Lit>> &clauses, int nbVar, int lim_solver,
                    StringOption &definabilitySort, int lim_occ, bool useGates,
                    vec<Var> &protectedVar) {
  Solver S;
  while (S.nVars() < nbVar)
    S.newVar();
  for (int i = 0; i < clauses.size(); i++)
    S.addClause_(clauses[i]);
  if (!S.simplify() || !S.solve()) {
    printf("p cnf %d 2\n1 0\n-1 0\n", nbVar);
    exit(0);
  } // unsat formula

  // compute the backbone
  Backbone bb;
  bb.computeBackBone(S, S.model);

  // collect gates (if the option is activated)
  vec<vec<Lit>> gates, defGates;
  if (useGates) {
    GatesDetection gd(S);
    gd.collectGates(S, gates, protectedVar);
    for (int i = 0; i < gates.size(); i++) {
      defGates.push();
      gates[i].copyTo(defGates.last());
    }
  }

  // we compute a bi-partition
  rebuiltClauses(S, clauses);

  vec<Var> inputVars, outVars, forgetVariables;
  DefinableDetection fDec;
  fDec.collectBiPartition(clauses, nbVar, inputVars, outVars, lim_solver,
                          definabilitySort, defGates, protectedVar);
  vec<Lit> &unit = fDec.getUnitLit();
  for (int i = 0; i < unit.size(); i++)
    if (S.value(unit[i]) == l_Undef)
      S.uncheckedEnqueue(unit[i]);

  // debug
  for (int i = 0; i < outVars.size(); i++)
    for (int j = 0; j < protectedVar.size(); j++)
      if (outVars[i] == protectedVar[j]) {
        fprintf(stderr, "Erreur, I removed a protected variables oO\n");
        exit(7);
      }

  // we forget output variables
  Forgetting fo(S);
  fo.runForgetting(outVars, forgetVariables, lim_occ, gates, useGates);

  vec<vec<Lit>> reduceClauses;
  S.computeSimplifiedFormula(reduceClauses);
  showInstanceAfterPreproc(reduceClauses, forgetVariables, S.trail, nbVar);

  exit(0);
} // appliedPreproc

//=================================================================================================
// Main:

int main(int argc, char **argv) {
  printf("c\nc This is glucose 3.0 --  based on MiniSAT (Many thanks to "
         "MiniSAT team)\nc\n");
  try {
    setUsageHelp("c USAGE: %s [options] <input-file> <result-output-file>\n\n "
                 "where input may be either in plain or gzipped DIMACS.\n");

#if defined(__linux__)
    fpu_control_t oldcw, newcw;
    _FPU_GETCW(oldcw);
    newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE;
    _FPU_SETCW(newcw);
    printf(
        "c WARNING: for repeatability, setting FPU to use double precision\n");
#endif
    // Extra options:
    //
    IntOption verb("MAIN", "verb",
                   "Verbosity level (0=silent, 1=some, 2=more).", 1,
                   IntRange(0, 2));
    BoolOption mod("MAIN", "model", "show model.", false);
    IntOption vv("MAIN", "vv", "Verbosity every vv conflicts", 10000,
                 IntRange(1, INT32_MAX));
    IntOption lim_solver(
        "MAIN", "lim-solver",
        "Limit the solver for definability (0 means no limit).\n", 0,
        IntRange(0, INT32_MAX));
    IntOption lim_occ("MAIN", "max#Res",
                      "Limit the maximal number of authorized resolution.\n",
                      500, IntRange(0, INT32_MAX));

    BoolOption callOracle("MAIN", "oracle", "Call the SAT oracle.", false);
    BoolOption callPreproc("MAIN", "preproc", "Call the preprocessor.", false);
    BoolOption useGates(
        "MAIN", "useGate",
        "Using the gates detection in the bi-partition process.", false);

    StringOption onlyB("MAIN", "B", "Only compute a set of input variables",
                       "/dev/null");
    StringOption onlyE("MAIN", "E",
                       "Forget a set of variables given in parameter",
                       "/dev/null");
    StringOption definabilitySort(
        "MAIN", "definabilitySort",
        "Heuristics implemented: NATURAL_ORDER, OCC_ASC, GEN_TAUTS", "OCC_ASC");

    parseOptions(argc, argv, true);

    if (argc == 1)
      printf("c Reading from standard input... Use '--help' for help.\n");

    gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
    if (in == NULL)
      printf("c ERROR! Could not open file: %s\n",
             argc == 1 ? "<stdin>" : argv[1]),
          exit(1);

    int nbVar = 0;
    double initial_time = cpuTime();
    vec<QuantifBlock> listQuantif;
    vec<Var> protectedVar;

    vec<vec<Lit>> clauses;
    nbVar = parse_DIMACS(in, clauses, listQuantif, protectedVar);
    gzclose(in);

    double parsed_time = cpuTime();
    if (verb)
      printf("c Parse time (seconds): %12.2f\nc\n", parsed_time - initial_time);

    if (onlyB != "/dev/null")
      appliedB(clauses, nbVar, lim_solver, definabilitySort, onlyB, useGates,
               protectedVar);
    else if (onlyE != "/dev/null")
      appliedE(clauses, nbVar, lim_occ, onlyE, useGates, protectedVar);
    else if (callPreproc)
      appliedPreproc(clauses, nbVar, lim_solver, definabilitySort, lim_occ,
                     useGates, protectedVar);
    else
      return satOracle(clauses, nbVar, mod, verb, vv);

  } catch (OutOfMemoryException &) {
    printf("c "
           "==================================================================="
           "================================\n");
    printf("INDETERMINATE\n");
    exit(0);
  }
}
