/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.MLS
import AvgCaseMls.AvCom

/-!
Structural statement of average-case hardness for MLS satisfiability.

Extracted from [`arxiv.md`](../arxiv.md) §9. Proof is intentionally incomplete (`sorry`).
-/

open MLS AvCom

axiom NEXP_neq_EXP : Prop

axiom serializeFormula : MLS.Formula → Bitstring

def SatMLS : Set Bitstring :=
  { s | ∃ (f : MLS.Formula), serializeFormula f = s ∧ ∃ (env : MLS.Env), MLS.evalFormula env f }

/-
  Theorem 5.1 (adapted): SatMLS is NP-average complete.
  Consequently, there exists a simple, polynomial-time rankable distribution μ
  under which (SatMLS, μ) is not in AvP, assuming NEXP ≠ EXP.
-/
theorem SatMLS_average_hard
    (μ : Distribution)
    (h_rank : ∃ T, IsPolynomial T ∧ ∀ x, rank μ x ≤ T (len x)) :
    NEXP_neq_EXP → ¬ AvP ⟨SatMLS, μ⟩ := by
  intro h_collapse h_avp
  sorry
