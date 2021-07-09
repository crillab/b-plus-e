#include <iostream>

#include "utils/System.h"
#include "mtl/Sort.h"
#include "mtl/Vec.h"
#include "mtl/Heap.h"
#include "mtl/Alg.h"
#include "core/Dimacs.h"
#include "core/SolverTypes.h"
#include "core/Solver.h"
#include "core/GatesDetection.h"
#include "core/DefinableDetection.h"

using namespace std;
using namespace Glucose;

#define CRITICAL 0


/**
   Sort the set of selectors given in parameter.
*/
void DefinableDetection::sortSelectorsOccDesc(Solver &solver, vec<Lit> &selectors, vec<Lit> &assums, int initNbVar, vec<vec<Lit> > &cls)
{
  coupleLit occList[initNbVar], fitSelector[selectors.size()];

  // we don't care the positive phase ... we save the lit in the same place as the var
  for(int i = 0 ; i<initNbVar ; ++i) occList[i] = {mkLit((initNbVar<<1) + i, false), 0}; 

  for(int i = 0 ; i<cls.size() ; i++)
    {
      vec<Lit> &cl = cls[i];
      for(int j = 0 ; j<cl.size() ; j++) occList[var(cl[j])].nbOcc++;
    }

  for(int i = 0 ; i<selectors.size() ; i++)
    {
      fitSelector[i] = occList[var(selectors[i]) - (initNbVar<<1)] ;
      assert(fitSelector[i].l == selectors[i]);
    }
      
  qsort(fitSelector, selectors.size(), sizeof(coupleLit), lt_coupleLit);
  for(int i = 0 ; i<selectors.size() ; ++i) assums.push(fitSelector[i].l);
}// sortSelectorsOccDesc


void DefinableDetection::sortSelectorsTautologyGeneration(Solver &solver, vec<Lit> &selectors, int initVarNum, vec<Lit> &assums,
                                             vec<vec<Lit> > &cls)
{
  int **associatedWith = new int*[(initVarNum<<1)];
  for(int i=0; i<(initVarNum<<1); ++i)
    {
      associatedWith[i] = new int[(initVarNum<<1)];
      for(int j=0; j<initVarNum<<1; ++j) associatedWith[i][j]=0;
    }

  vec<CRef> &initClauses = solver.clauses;
  for(int clIndex=0; clIndex<initClauses.size(); ++clIndex)
    {
      Clause &cl = solver.ca[initClauses[clIndex]];
      for(int litIndex=0; litIndex<cl.size(); ++litIndex)
        {
          for(int litIndex2=0; litIndex2<cl.size(); ++litIndex2)
            {
              if(litIndex==litIndex2) continue;
              int associatedWithIndex = sign(cl[litIndex])==false?(var(cl[litIndex])<<1):1+(var(cl[litIndex])<<1);
              int associatedWithLiteralIndex = sign(cl[litIndex2])==false?(var(cl[litIndex2])<<1):1+(var(cl[litIndex2])<<1);
              ++associatedWith[associatedWithIndex][associatedWithLiteralIndex];
            }//lit2 selection
        }//lit1 selection
    }// clause selection
      
  int *tauts = new int[initVarNum<<1];
  for(int i=0; i<initVarNum; ++i)
    {
      tauts[i<<1] = i;
      tauts[1+(i<<1)] = 0;
      for(int j=0; j<initVarNum; ++j)
        {
          if(i==j) continue;
          tauts[(i<<1)+1]  = associatedWith[(i<<1)][(j<<1)]*associatedWith[(i<<1)+1][(j<<1)+1];
          tauts[(i<<1)+1] += associatedWith[(i<<1)+1][(j<<1)]*associatedWith[(i<<1)][(j<<1)+1];
        }
    }
      
  qsort(tauts, initVarNum, sizeof(int)<<1, sortOccListDesc);
  int *selArray = new int[initVarNum];
  for(int i=0; i<initVarNum; ++i) selArray[i] = 0;
  for(int i=0; i<selectors.size(); ++i) selArray[var(selectors[i])-(initVarNum<<1)] = 1;
  for(int i=0; i<initVarNum; ++i)
    {
      if(selArray[tauts[i<<1]])
        {
          assums.push(mkLit(tauts[i]+(initVarNum<<1),false));
        }
    }
  delete[] selArray;
  delete[] tauts;
  for(int i=0; i<(initVarNum<<1); ++i)
    {
      delete[] associatedWith[i];
    }
  delete[] associatedWith;
}// sortSelectorsTautologyGeneration



/**
   Add a set of equivalences controlled by selectors. More
   precisly we have ~selectors[i] v (v1[i]] <-> v2[i]).
       

   @param[out] solver, the solver where are added the clauses
   @param[in] v1, the first set of variables       
   @param[in] v2, the second set of variables
   @param[out] selectors, the set of literal that activate the equivalences
*/
void DefinableDetection::addSelectedEquivalence(Solver &solver, vec<Var> &v1, vec<Var> &v2, vec<Lit> &selectors)
{
  assert(v1.size() == v2.size());
      
  // Second: we add the equivalence clauses
  for(int i = 0 ; i<v1.size() ; i++)
    {
      solver.newVar(); 
      if(solver.value(v1[i]) != l_Undef) continue;
      selectors.push(mkLit(solver.nVars() - 1, false));          
          
      for(int j = 0 ; j<2 ; j++)
        {
          vec<Lit> phClause;
          phClause.push(~selectors.last());
          phClause.push(mkLit(v1[i], 1 - j));
          phClause.push(mkLit(v2[i], j));
              
          solver.addClause_(phClause); // the clause is safe 
        }          
    }
}// addSelectedEquivalence


/**
   Duplicate and shift the input formula
   @param[out] solver, the solver where are added the clauses
   @param[in] cls, the set of clauses
   @param[in] shift, the shift value
*/
void DefinableDetection::addShiftFormula(Solver &solver, vec<vec<Lit> > &cls, int shift)
{       
  // we add the duplicate formula
  for(int i = 0 ; i<cls.size() ; i++)
    {
      vec<Lit> &cl = cls[i], phClause;
      bool isSAT = false;
          
      for(int j = 0 ; j<cl.size() && !isSAT ; j++)
        {
          while(solver.nVars() <= (var(cl[j]) + shift)) solver.newVar();
          if(solver.value(cl[j]) == l_Undef)  phClause.push(mkLit(var(cl[j]) + shift, sign(cl[j])));
          else isSAT = solver.value(cl[j]) == l_True;
        }
          
      if(isSAT) continue;
      assert(phClause.size());
      solver.addClause_(phClause); // the clause is safe 
    }
}// addShiftFormula


/**
   Compute the backbone.
*/
void DefinableDetection::computeBackBone(Solver &solver, vec<lbool> &currentModel)
{
  double initTime = cpuTime();
  int cpt = (solver.trail).size();
  
  for(int v = 0 ; v<solver.nVars() ; v++)
    {       
      // l is implied?
      if(solver.value(v) != l_Undef || currentModel[v] == l_Undef) continue;
      Lit l = mkLit(v, currentModel[v] == l_False);
      
      if(!solver.solve(~l)){if(solver.value(l) == l_Undef) solver.uncheckedEnqueue(l);}
      else
        {
          for(int i = v ; i<solver.nVars() ; i++)
            if(currentModel[i] != solver.model[i]) currentModel[i] = l_Undef;
        }
    }

  printf("c\nc Backbone simplification\n");
  printf("c The number of unit literal found is: %d\n", (solver.trail).size() - cpt);
  printf("c Time to realize the backbone simplification: %lf\n", cpuTime() - initTime);
}// computeBackBone



/**
   Compute a bi-partition using the classical constructive approach.

   @param[in] solver, a SAT oracle
   @param[in] assums, the set of selector we want to work on
   @param[in] nbVar, the initial number of variable (use for shifted)
   @param[out] i, the set of input variables computed
   @param[out] o, the set of output variables computed
   @param[in] limitC, the number of conflicts the solver is allowed to do
*/
void DefinableDetection::constructive(Solver &solver, vec<Lit> &assums, int nbVar,
                                      vec<Var> &i, vec<Var> &o, int limitC, vec< vec<Lit> > &gates)
{
  vec<bool> isInput;
  vec< vec<int> > occGates;
  for(int i = 0 ; i<nbVar ; i++){isInput.push(true); occGates.push();}
  for(int i = 0 ; i<gates.size() ; i++) occGates[var(gates[i][0])].push(i);
  printf("c The number of computed gates is: %d\n", gates.size());
  
  while(assums.size())
    {
      Lit l = selectAndRemove(assums);
      solver.cancelUntil(assums.size());

      Var vc = var(l) - (nbVar<<1);
      bool definable = !isProtected[vc] && solver.value(l) != l_Undef;

      if(!isProtected[vc] && !definable)
        {
          assums.push(mkLit(var(l) - (nbVar<<1), true));
          assums.push(mkLit(var(l) - nbVar, false));

          for(int i = 0 ; !definable && i<occGates[vc].size() ; i++)
            {
              vec<Lit> &g = gates[occGates[vc][i]];              
              if(!g.size()) continue;
              
              definable = true;
              for(int j = 1 ; definable && j<g.size() ; j++) definable = isInput[var(g[j])];
            }
                   
          if(!definable) definable = (solver.solveLimited(assums, limitC) == l_False);
          else assert(solver.solveLimited(assums, limitC) == l_False);
          assums.pop(); assums.pop();          
        }
      
      if(assums.size() < 500) solver.cancelUntil(0);
      if(!definable) 
        {
          solver.cancelUntil(0);    
          i.push(var(l) - (nbVar<<1));
          solver.uncheckedEnqueue(l, CRef_Undef);
        }else
        {
          for(int i = 0 ; i<occGates[vc].size() ; i++) gates[occGates[vc][i]].clear();
          isInput[vc] = false;
          o.push(var(l) - (nbVar<<1));
          if(!solver.decisionLevel() && solver.value(l) == l_Undef) solver.uncheckedEnqueue(~l, CRef_Undef);
        }
    }
}// constructive



/**
   Realize a variable bi-partition i/o such that for each variable x
   of o it exists Y variables of i such that x can be defined from Y.

   /!\ We suppose the problem satisfiable

   @param[in] cls, the set of clauses
   @param[in] nbVar, the number of variables
   @param[out] i, the computed input variables
   @param[out] o, the computed output variables
   @param[in] limitC, the number of conflicts that can realize the oracle
   @param[in] defSort, the heuristic used to sort the variables (selectors)
*/
void DefinableDetection::collectBiPartition(vec<vec<Lit> > &cls, int nbVar, vec<Var> &i, vec<Var> &o, int limitC,
                                            const char *defSort, vec< vec<Lit> > &gates, vec<Var> &protectedVar)
{
  printf("c\nc \033[33mCollect Bi-Partition Procedure\033[0m\n");
  double collectBiPartition_time = cpuTime();
  vec<Lit> selectors, assums;

  // prepare the solver
  Solver solver;
  solver.setIncrementalMode();
  solver.verbosity = solver.verbEveryConflicts = 0;
  solver.showModel = 1;
  solver.setIncrementalMode();
  
  // verify if the matrix is satisfiable
  while(solver.nVars() < nbVar)
    {
      isProtected.push(false);
      solver.newVar();
    }

  for(int i = 0 ; i<protectedVar.size() ; i++) isProtected[protectedVar[i]] = true; 
  for(int i = 0 ; i<cls.size() ; i++) solver.addClause_(cls[i]);

  addShiftFormula(solver, cls, nbVar);
  while(solver.nVars() < (nbVar<<1)) solver.newVar();

  // create the equivalences
  vec<Var> v1, v2;
  for(int i = 0 ; i<nbVar ; i++){ v1.push(i); v2.push(i + nbVar);}
  addSelectedEquivalence(solver, v1, v2, selectors);
  
  // define an order for the selectors
  if(!strcmp("NATURAL_ORDER", defSort)) sortSelectorsDummy(selectors, assums);
  else if(!strcmp("OCC_ASC", defSort)) sortSelectorsOccDesc(solver, selectors, assums, nbVar, cls);
  else sortSelectorsTautologyGeneration(solver, selectors, nbVar, assums, cls);
  printf("c Time to sort the selector: %lf\n", cpuTime() - collectBiPartition_time);      
      
  // here we compute the definable bi-partition
  constructive(solver, assums, nbVar, i, o, limitC, gates);
   
  // print information
  printf("c Number of input variables computed: %d\n", i.size());
  printf("c Time to compute the bi-partition: %lf\n", cpuTime() - collectBiPartition_time);
  printf("c\n");
}// collectBiPartition


