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
#include "core/Backbone.h"

using namespace std;
using namespace Glucose;


/**
   Compute the backbone.
*/
void Backbone::computeBackBone(Solver &solver, vec<lbool> &currentModel)
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

