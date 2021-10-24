
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
/****************************************************************************************[Dimacs.h]
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

#ifndef Glucose_Dimacs_h
#define Glucose_Dimacs_h

#include <stdio.h>

#include "core/SolverTypes.h"
#include "utils/ParseUtils.h"

namespace Glucose {

struct QuantifBlock {
  vec<Var> vars;
  bool isExist;
};

//=================================================================================================
// DIMACS Parser:

template <class B> static void readClause(B &in, vec<Lit> &lits, int &maxIdx) {
  int parsed_lit, var;
  lits.clear();
  for (;;) {
    parsed_lit = parseInt(in);
    if (parsed_lit == 0)
      break;
    var = abs(parsed_lit) - 1;
    lits.push((parsed_lit > 0) ? mkLit(var) : ~mkLit(var));

    if (var + 1 > maxIdx)
      maxIdx = var + 1;
  }
} // readClause

template <class B>
static void parse_DIMACS_main(B &in, vec<vec<Lit>> &cls,
                              vec<QuantifBlock> &listQuantif, int &maxIdx,
                              vec<Var> &inputVar, vec<Var> &outputVar) {
  vec<Lit> lits;
  int cnt = 0, vars = 0, clauses = 0;
  for (;;) {
    skipWhitespace(in);
    if (*in == EOF)
      break;
    else if (*in == 'p') {
      if (eagerMatch(in, "p cnf")) {
        vars = parseInt(in); // consume var
        maxIdx = vars;
        clauses = parseInt(in); // consume clause
      } else
        printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
    } else if (*in == 'a' || *in == 'e') {
      int parsed_lit;

      listQuantif.push();
      QuantifBlock &q = listQuantif.last();

      q.isExist = *in == 'e' || *in == 'E';
      vec<Var> &v = q.vars;
      ++in;

      for (;;) {
        parsed_lit = parseInt(in);
        if (parsed_lit == 0)
          break;
        v.push(abs(parsed_lit) - 1);
      }
    } else if (*in == 'c') {
      ++in;
      if (*in == ' ') {
        ++in;
        char save = *in;
        if (save == 'i' || save == 'o') {
          ++in;
          int parsed_lit;
          for (;;) {
            parsed_lit = parseInt(in);
            if (parsed_lit == 0)
              break;

            if (save == 'i')
              inputVar.push(abs(parsed_lit) - 1);
            else
              outputVar.push(abs(parsed_lit) - 1);
          }
        } else
          skipLine(in);
      } else
        skipLine(in);
    } else if (*in == 'p' || *in == 'w')
      skipLine(in);
    else {
      cnt++;
      cls.push();
      readClause(in, cls.last(), maxIdx);
    }
  }

  if (vars != maxIdx)
    fprintf(stderr,
            "WARNING! DIMACS header mismatch: wrong number of variables.\n");
  if (cnt != clauses)
    fprintf(stderr,
            "WARNING! DIMACS header mismatch: wrong number of clauses.\n");
}

// Inserts problem into solver.
static int parse_DIMACS(gzFile input_stream, vec<vec<Lit>> &cls,
                        vec<QuantifBlock> &listQuantif, vec<Var> &inputVar,
                        vec<Var> &outputVar) {
  StreamBuffer in(input_stream);
  int maxIdx = 0;
  parse_DIMACS_main(in, cls, listQuantif, maxIdx, inputVar, outputVar);
  return maxIdx;
}
} // namespace Glucose

#endif
