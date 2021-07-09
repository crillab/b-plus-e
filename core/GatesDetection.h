#ifndef GLUCOSE_SOLVER_GATES_DETECTION
#define GLUCOSE_SOLVER_GATES_DETECTION

#include <cstring>
#include "core/Solver.h"

namespace Glucose
{
  class GatesDetection
  {
  private:
    Solver &solver;
    vec<bool> isProtected;
    
    vec<int> flags;
    void collectBinaryAdj(Solver &solver, vec< vec<Lit> > &listPU);
    void collectBinaryAdjLit(Solver &solver, vec<Lit> &listPU, Lit l);
    
  public:
  GatesDetection(Solver &s) : solver(s) {}
    
    void searchOrGateFromLit(Solver &solver, vec<Lit> &og, Lit l, vec< vec<int> > &occurrences);
    void collectGates(Solver &solver, vec< vec<Lit> > &gates, vec<Var> &protectedVar);
    void collectBinaryEquivalence(Solver &solver, vec< vec<Lit> > &listOfOrGates, Lit l);
    void collectOrGates(Solver &solver, vec< vec<Lit> > &listOfOrGates);
  
  };
}


#endif
