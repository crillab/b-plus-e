/****************************************************************************************[Dimacs.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Glucose_Dimacs_h
#define Glucose_Dimacs_h

#include <stdio.h>

#include "utils/ParseUtils.h"
#include "core/SolverTypes.h"

namespace Glucose {

  struct QuantifBlock
  {
    vec<Var> vars;
    bool isExist;
  };

  
  //=================================================================================================
  // DIMACS Parser:

  template<class B> static void readClause(B& in, vec<Lit>& lits, int &maxIdx) 
  {
    int parsed_lit, var;
    lits.clear();
    for (;;)
      {
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit) - 1;
        lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );

        if(var + 1 > maxIdx) maxIdx = var + 1;
      }
  }// readClause

  
  template<class B> static void parse_DIMACS_main(B& in, vec<vec<Lit> > &cls,  vec<QuantifBlock> &listQuantif,
                                                  int &maxIdx, vec<Var> &protectedVar) 
  {
    vec<Lit> lits;
    int cnt = 0, vars = 0, clauses = 0;
    for (;;)
      {
        skipWhitespace(in);
        if (*in == EOF) break;
        else if (*in == 'p')
          {          
            if(eagerMatch(in, "p cnf"))
              {
                vars = parseInt(in); // consume var
                maxIdx = vars;
                clauses = parseInt(in); // consume clause
              }else printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
          }
        else if (*in == 'a' || *in == 'e')
          {
            int parsed_lit;
           
            listQuantif.push();
            QuantifBlock &q = listQuantif.last();

            q.isExist = *in == 'e' || *in == 'E';
            vec<Var> &v = q.vars;
            ++in;
           
            for ( ; ; )
              {
                parsed_lit = parseInt(in);
                if(parsed_lit == 0) break;
                v.push(abs(parsed_lit) - 1);
              }
          } else if (*in == 'c')
          {
            ++in;
            if(*in == ' ')
              {
                ++in;
                if(*in == 't')
                  {
                    ++in;
                    int parsed_lit;
                    for ( ; ; )
                      {
                        parsed_lit = parseInt(in);
                        if(parsed_lit == 0) break;
                        protectedVar.push(abs(parsed_lit) - 1);
                      }
                  }else skipLine(in);
              }else skipLine(in);
          } else if (*in == 'p' || *in == 'w') skipLine(in);
        else
          {
            cnt++;
            cls.push();
            readClause(in, cls.last(), maxIdx);
          }
      }

    if (vars != maxIdx) fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of variables.\n");
    if (cnt  != clauses) fprintf(stderr, "WARNING! DIMACS header mismatch: wrong number of clauses.\n");
  }
 
  // Inserts problem into solver.
  static int parse_DIMACS(gzFile input_stream, vec<vec<Lit> > &cls, vec<QuantifBlock> &listQuantif, vec<Var> &protectedVar) 
   {
     StreamBuffer in(input_stream);
     int maxIdx = 0;
     parse_DIMACS_main(in, cls, listQuantif, maxIdx, protectedVar);
     return maxIdx;
   }
}

#endif
