#ifndef GLUCOSE_SOLVER_BACKBONE
#define GLUCOSE_SOLVER_BACKBONE

#include <cstring>

namespace Glucose
{
  class Backbone
  {    
  public:
    void computeBackBone(Solver &solver, vec<lbool> &currentModel);
  };
}


#endif
