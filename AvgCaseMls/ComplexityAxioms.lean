/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.AvCom

open AvCom

/-!
Explicit complexity-collapse interface for conditional average-case hardness.

Mathlib does not yet define the required complexity classes. Instead of global
project axioms, downstream conditional theorems take this interface as an
explicit argument.
-/

/--
The exact external principles used by the legacy conditional-hardness chain.
Supplying this structure is an explicit proof obligation.
-/
structure AverageCaseCollapseTheory where
  NEXP_eq_EXP : Prop
  distNP_subseteq_AvP_iff_NEXP_eq_EXP :
  (∀ p, InDistNP p → AvP p) ↔ NEXP_eq_EXP
  AvP_pullback {source target : DistributionalProblem}
    (hAvP : AvP target) (hRed : DistributionalReduction source target) :
    AvP source

namespace AverageCaseCollapseTheory

/-- The explicit separation assumption relative to a supplied class model. -/
def NEXP_neq_EXP (theory : AverageCaseCollapseTheory) : Prop :=
  ¬ theory.NEXP_eq_EXP

end AverageCaseCollapseTheory
