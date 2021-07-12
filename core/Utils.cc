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

#include "core/Utils.h"
#include <stdio.h>

namespace Glucose {

vec<int> Utils::buffer;

int Utils::joinArrays(int *p1, int *p2, int *p3) {
  int **min, last = 0, *pBuffer = buffer, *res = p1;

  if (!*p1)
    min = &p1;
  else if (!*p2)
    min = &p2;
  else if (!*p3)
    min = &p3;
  else
    for (;; (*min)++) {
      // Look for min value
      if (*p1 < *p2) {
        if (*p1 < *p3)
          min = &p1;
        else
          min = &p3;
      } else {
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

  if (!*p1)
    min = &p1;
  else if (!*p2)
    min = &p2;
  else
    for (;; (*min)++) {
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

  for (; *p1; p1++) {
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
  for (res += last - 1; pBuffer != (buffer - 1);)
    *res-- = *pBuffer--;

  return last;
}

void Utils::initBuffer(int size) { buffer.capacity(size); }

}; // namespace Glucose
