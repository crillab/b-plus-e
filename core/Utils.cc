
#include <stdio.h>
#include "core/Utils.h"

namespace Glucose
{

vec<int> Utils::buffer;
    
int Utils::joinArrays(int *p1, int *p2, int *p3) {
    int **min, last = 0, *pBuffer = buffer, *res = p1;
    
    if (!*p1)      min = &p1;
    else if (!*p2) min = &p2;
    else if (!*p3) min = &p3;
    else
    for ( ; ; (*min)++ ) {
        // Look for min value
        if (*p1 < *p2) {
            if (*p1 < *p3)
                min = &p1;
            else
                min = &p3;
        }
        else {
            if (*p2 < *p3)
                min = &p2;
            else
                min = &p3;
        }

        // INSERT min element
        if (**min != last) {
            last = **min;
            *(pBuffer++) = last;
        }

        // Exit the loop
        if (!*(*min + 1)) {
            break;
        }
    }

    // Keeps 2 pointers p1 and p2
    if (*min == p1)
        p1 = p3;
    else if (*min == p2)
        p2 = p3;
    
    
    if (!*p1)      min = &p1;
    else if (!*p2) min = &p2;
    else
    for ( ; ; (*min)++ ) {
        // Look for min value
        if (*p1 < *p2)
            min = &p1;
        else
            min = &p2;
        
        // INSERT min element
        if (**min != last) {
            last = **min;
            *(pBuffer++) = last;
        }

        // Exit the loop, keeping 1 pointer p1
        if (!*(*min + 1)) {
            if (*min == p1)
                p1 = p2;
            break;
        }
    }
    
    
    for ( ; *p1 ; p1++) {
        // INSERT min element
        if (*p1 != last)
            *(pBuffer++) = *p1;
        
        // Exit the loop, keeping 1 pointer p1
        if (!(*min + 1))
            break;
    }
    

    // Put in variable last the number of variables
    last = pBuffer-- - buffer;
    
    // Copy buffer into res
    for (res += last - 1 ; pBuffer != (buffer - 1) ; ) *res-- = *pBuffer--;
    
    return last;
    
}


  void Utils::initBuffer(int size){buffer.capacity(size);}

};
