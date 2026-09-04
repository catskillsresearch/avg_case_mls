/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import Mathlib.Analysis.PSeries
import AvgCaseMls.AvCom
import AvgCaseMls.Section3.TR1995

/-!
# Numbered results from Cox–Ericson–Mishra (1995)

This module is the paper-aligned home for the numbered statements in
TR1995-711.  Statements follow `sources/TR1995-711_vision.md`; cited proofs are
cross-checked against the dependency transcriptions in `sources/`.

Only results whose mathematical content is represented by the current
definitions belong here.  In particular, no theorem is obtained by hiding a
paper hypothesis or an unproved complexity result in a definition.
-/

namespace TR1995

open AvCom

/-! ## Theorem 4.1 -/

/--
Paper-level NP-average completeness of a language: every distributional NP
source reduces to the language under some polynomially rankable target
distribution.
-/
def IsNPAverageCompleteLanguage (L : Set Bitstring) : Prop :=
  InNP L ∧
    ∀ source : DistributionalProblem, InDistNP source →
      ∃ μ : Distribution,
        IsPolRankable μ ∧ DistributionalReduction source ⟨L, μ⟩

/--
**Theorem 4.1.** If one fixed distribution makes `(L, ρ)`
NP-distributional complete, then `L` is NP-average complete.
-/
theorem theorem_4_1 {L : Set Bitstring} {ρ : Distribution}
    (h : IsNPAverageComplete ⟨L, ρ⟩) :
    IsNPAverageCompleteLanguage L := by
  refine ⟨h.1.1, ?_⟩
  intro source hsource
  exact ⟨ρ, h.1.2, h.2 source hsource⟩

/-! ## Example 4.1

For strings of length `n`, the standard distribution contributes total mass
proportional to `n⁻²`.  If the machine takes `n²` steps and the proposed
average-time bound has exponent `1 + ε`, applying its inverse contributes
`n^(2/(1+ε))`; division by input length leaves the p-series exponent below.
-/

/-- The exponent of the length-shell contribution in Example 4.1. -/
noncomputable def example41Exponent (ε : ℝ) : ℝ :=
  -3 + 2 / (1 + ε)

/--
The length-shell contribution in Example 4.1, including the standard
distribution's normalizing factor `6 / π²`.
-/
noncomputable def example41Contribution (ε : ℝ) (n : Nat) : ℝ :=
  (6 / Real.pi ^ 2) * (n : ℝ) ^ example41Exponent ε

/--
The report's standard mass, with zero assigned to the empty string.

This is declared here, immediately after `example41Exponent` and
`example41Contribution`, to mirror `Challenge.lean`'s declaration order.  The
`6` and `2` literals need `Nat.AtLeastTwo` instance proofs, which Lean lifts
into `_proof_*` auxiliaries that are reused only within a single module.  In
`Challenge.lean` this definition reuses the two auxiliaries created just above;
declaring it in a separate module makes it mint its own, and Palomar's
elaborated-term comparison rejects the submission.
-/
noncomputable def _root_.Example41.standardMass (x : List Bool) : ℝ :=
  if x.isEmpty then 0
  else (6 / Real.pi ^ 2) * (x.length : ℝ) ^ (-2 : ℝ) / (2 : ℝ) ^ x.length

theorem example41Exponent_lt_neg_one {ε : ℝ} (hε : 0 < ε) :
    example41Exponent ε < -1 := by
  have hden : 0 < 1 + ε := by linarith
  have hfrac : 2 / (1 + ε) < 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  unfold example41Exponent
  linarith

/--
**Example 4.1 (analytic core).** For every `ε > 0`, the rank/length-shell
series produced by a quadratic-time machine under the standard distribution,
when tested against an `n^(1+ε)` Levin bound, converges.

This is the precise p-series calculation behind the report's observation that
the original probability-weighted definition understates the quadratic
running time as `O(n^(1+ε))` for arbitrary positive `ε`.
-/
theorem example_4_1 {ε : ℝ} (hε : 0 < ε) :
    Summable (example41Contribution ε) := by
  have hp : Summable (fun n : Nat => (n : ℝ) ^ example41Exponent ε) :=
    (Real.summable_nat_rpow).2 (example41Exponent_lt_neg_one hε)
  exact hp.mul_left (6 / Real.pi ^ 2)

/--
The convergent shell calculation can be scaled by a positive constant so that
it satisfies Levin's normalized `≤ 1` requirement.  This is the formal content
of the big-O constant hidden in `O(n^(1+ε))`.
-/
theorem example_4_1_normalized {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      Summable (example41Contribution ε) ∧
      (∑' n : Nat, example41Contribution ε n / C) ≤ 1 := by
  have hsum := example_4_1 hε
  let S := ∑' n : Nat, example41Contribution ε n
  let C := max S 1
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hsum, ?_⟩
  rw [tsum_div_const]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one (le_max_right S 1))).2
    (le_max_left S 1)

end TR1995
