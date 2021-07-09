#ifndef GLUCOSE_SolverUtils_h
#define GLUCOSE_SolverUtils_h

#include <assert.h>
#include "mtl/Vec.h"

namespace Glucose
{
  class Utils
  {
  private:
    static vec<int> buffer;
        
    static void merge_(int *arr, int size1, int size2);
    static void mergeSort_(int *arr, int size);
        

  public:
    // End of array
    static const int EOA = -1;
        
    static void initBuffer(int size);
        
    /*
      This method joins efficiently 3 ordered vectors keeping order
      
      @param[in] p1: first vector to join
      @param[in] p2: second vector to join
      @param[in] p3: third vector to join
    */
    static int joinVectors(vec<int> p1, vec<int> p2, vec<int> p3);
    static int joinArrays(int *p1, int *p2, int *p3);
        
    /* 
       IMPORTANT: method initMemory must be called at least once
       before with size parameter greater or equal to the size of the
       array to sort
     */
    static void sort(vec<int> arr);
    static void sort(int *arr, int size);
  };
  
  
    
  // Inline methods
  inline int Utils::joinVectors(vec<int> p1, vec<int> p2, vec<int> p3)
  {
    p1.push(0); p2.push(0); p3.push(0);
    int res = Utils::joinArrays(p1, p2, p3);
    p1.pop(); p2.pop(); p3.pop();
    return res;
  }

  inline void Utils::sort(vec<int> arr)
  {
    mergeSort_(arr, arr.size());
  }
    
  inline void Utils::sort(int *arr, int size)
  {
      if (size) mergeSort_(arr, size);
  }
};
    
#endif
