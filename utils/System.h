
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
/****************************************************************************************[System.h]
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

#ifndef Glucose_System_h
#define Glucose_System_h

#if defined(__linux__)
#include <fpu_control.h>
#endif

#include "mtl/IntTypes.h"

//-------------------------------------------------------------------------------------------------

namespace Glucose {

static inline double cpuTime(void); // CPU-time in seconds.
extern double
memUsed(); // Memory in mega bytes (returns 0 for unsupported architectures).
extern double memUsedPeak(); // Peak-memory in mega bytes (returns 0 for
                             // unsupported architectures).

} // namespace Glucose

//-------------------------------------------------------------------------------------------------
// Implementation of inline functions:

#if defined(_MSC_VER) || defined(__MINGW32__)
#include <time.h>

static inline double Glucose::cpuTime(void) {
  return (double)clock() / CLOCKS_PER_SEC;
}

#else
#include <sys/resource.h>
#include <sys/time.h>
#include <unistd.h>

static inline double Glucose::cpuTime(void) {
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000;
}

#endif

#endif
