/*
 Institute for Formal Models and Verification (FMV),
 Johannes Kepler University Linz, Austria
 
 Copyright (c) 2006, Robert Daniel Brummayer
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice,
      this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice,
      this list of conditions and the following disclaimer in the documentation
      and/or other materials provided with the distribution.
    * Neither the name of the FMV nor the names of its contributors may be
      used to endorse or promote products derived from this software without
      specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE
 FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
#ifndef _SAT_SOLVER_H_
#define _SAT_SOLVER_H_

/** @brief Represents an adapter for a SAT solver. */
struct SatSolver
{
  /** The SAT solver */
  void *solver;
  /** The name of the SAT solver */
  char *name;
  /** The value which means satisfiable */
  int sat_val;
  /** The value which means unsatisfiable */
  int unsat_val;
  /** The initialisation function of the sat solver  */
  void *(*ptr_sat_solver_init) (void);
  /** The clean up function of the sat solver  */
  void (*ptr_sat_solver_finalise) (void *solver);
  /** The SAT function which returns if the input is
   * satisfiable or not
   */
  int (*ptr_sat_solver_sat) (void *solver);
  /** The add function which is used for adding CNF clauses */
  void (*ptr_sat_solver_add) (void *solver, int x);
  /** The dereference function which is used for retrieving
   * the satisfying assignment of a boolean variable if the
   * result is satisfiable */
  int (*ptr_sat_solver_deref) (void *solver, int x);
};

typedef struct SatSolver SatSolver;

/** Creates the adapter for the currently installed SAT solver
 * and returns it.
 * @return The SAT solver adapter
 */
SatSolver *create_sat_solver ();

/** Deletes the SAT solver adapter from memory.
 * @param sat_solver The sat solver adapter which has
 * to be deleted
 */
void delete_sat_solver (SatSolver * sat_solver);

#endif
