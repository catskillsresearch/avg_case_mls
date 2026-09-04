/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Foundation.Rankability

namespace AvgCaseMls.Foundation

/-- A machine together with a proof that its executable runs decide `L`. -/
structure Decider (L : Set Bitstring) where
  program : Program
  halts : ∀ x, ∃ fuel r, program.eval fuel x = some r
  correct_run :
    ∀ x fuel r, program.eval fuel x = some r → (r.accept = true ↔ x ∈ L)

namespace Decider

theorem decides (d : Decider L) : Decides d.program L := by
  intro x
  obtain ⟨fuel, r, hr⟩ := d.halts x
  exact ⟨r, ⟨fuel, hr⟩, d.correct_run x fuel r hr⟩

theorem terminates (d : Decider L) (x : Bitstring) :
    ∃ fuel r, d.program.eval fuel x = some r :=
  d.halts x

theorem eventually_isSome (d : Decider L) (x : Bitstring) :
    ∃ fuel, (d.program.eval fuel x).isSome = true := by
  obtain ⟨fuel, r, hr⟩ := d.terminates x
  exact ⟨fuel, by simp [hr]⟩

/-- Least fuel at which the executable evaluator returns a result. -/
noncomputable def haltingFuel (d : Decider L) (x : Bitstring) : Nat :=
  Nat.find (d.eventually_isSome x)

theorem haltingFuel_spec (d : Decider L) (x : Bitstring) :
    ∃ r, d.program.eval (d.haltingFuel x) x = some r := by
  have h := Nat.find_spec (d.eventually_isSome x)
  change (d.program.eval (d.haltingFuel x) x).isSome = true at h
  cases hopt : d.program.eval (d.haltingFuel x) x with
  | none =>
      simp only [hopt, Option.isSome_none] at h
      cases h
  | some r => exact ⟨r, rfl⟩

noncomputable def actualResult (d : Decider L) (x : Bitstring) : Result :=
  Classical.choose (d.haltingFuel_spec x)

theorem actualResult_spec (d : Decider L) (x : Bitstring) :
    d.program.eval (d.haltingFuel x) x = some (d.actualResult x) :=
  Classical.choose_spec (d.haltingFuel_spec x)

/-- Actual transition count of the least-fuel terminating execution. -/
noncomputable def actualRuntime (d : Decider L) (x : Bitstring) : Nat :=
  (d.actualResult x).steps

theorem actualResult_correct (d : Decider L) (x : Bitstring) :
    (d.actualResult x).accept = true ↔ x ∈ L := by
  exact d.correct_run x (d.haltingFuel x) (d.actualResult x) (d.actualResult_spec x)

end Decider

noncomputable def expectedCost (d : Decider L) (μ : Subprobability) : NNReal :=
  ∑' x, μ.prob x * d.actualRuntime x

def HasExpectedCostAtMost (d : Decider L) (μ : Subprobability) (bound : NNReal) : Prop :=
  Summable (fun x => μ.prob x * d.actualRuntime x) ∧ expectedCost d μ ≤ bound

/--
A monotone, unbounded complexity scale.  Unboundedness makes its generalized
inverse total; monotonicity gives it the intended least-threshold semantics.
-/
structure TimeScale where
  toFun : Nat → Nat
  monotone : Monotone toFun
  unbounded : ∀ m, ∃ n, m ≤ toFun n

instance : CoeFun TimeScale (fun _ => Nat → Nat) :=
  ⟨TimeScale.toFun⟩

namespace TimeScale

/-- Least `n` such that `m ≤ T(n)`. -/
noncomputable def inverse (T : TimeScale) (m : Nat) : Nat :=
  Nat.find (T.unbounded m)

theorem inverse_spec (T : TimeScale) (m : Nat) :
    m ≤ T (T.inverse m) :=
  Nat.find_spec (T.unbounded m)

theorem inverse_minimal (T : TimeScale) (m n : Nat) (h : m ≤ T n) :
    T.inverse m ≤ n :=
  Nat.find_min' (T.unbounded m) h

theorem inverse_monotone (T : TimeScale) : Monotone T.inverse := by
  intro m n hmn
  apply T.inverse_minimal
  exact hmn.trans (T.inverse_spec n)

end TimeScale

/--
A continuous nonnegative time scale together with its exact inverse.

The real-valued domain is needed for bounds such as `n^(1 + ε)`, whose
exponent need not be integral.  Requiring both inverse laws prevents an
arbitrary function from being presented as the inverse of a complexity scale.
-/
structure RealTimeScale where
  toFun : NNReal → NNReal
  inverse : NNReal → NNReal
  monotone : Monotone toFun
  left_inverse : Function.LeftInverse inverse toFun
  right_inverse : Function.RightInverse inverse toFun

instance : CoeFun RealTimeScale (fun _ => NNReal → NNReal) :=
  ⟨RealTimeScale.toFun⟩

namespace RealTimeScale

/--
The scale `(C n)^p`, with inverse `t^(1/p) / C`.

The factor `C` is placed inside the power so that dividing a Levin inverse by
`C` is represented by an actual time scale, rather than by an informal
normalization of the resulting series.
-/
noncomputable def scaledPower (p C : ℝ) (hp : 0 < p) (hC : 0 < C) :
    RealTimeScale where
  toFun n := (NNReal.mk C hC.le * n) ^ p
  inverse t := t ^ (1 / p) / NNReal.mk C hC.le
  monotone := by
    intro a b hab
    apply NNReal.rpow_le_rpow
    · exact mul_le_mul_of_nonneg_left hab (by positivity)
    · exact hp.le
  left_inverse := by
    intro n
    change ((NNReal.mk C hC.le * n) ^ p) ^ (1 / p) /
      NNReal.mk C hC.le = n
    rw [← NNReal.rpow_mul]
    have hp0 : p ≠ 0 := ne_of_gt hp
    have hmul : p * (1 / p) = 1 := by field_simp
    rw [hmul, NNReal.rpow_one]
    exact mul_div_cancel_left₀ n
      (ne_of_gt (show (0 : NNReal) < NNReal.mk C hC.le by exact hC))
  right_inverse := by
    intro t
    change (NNReal.mk C hC.le *
      (t ^ (1 / p) / NNReal.mk C hC.le)) ^ p = t
    rw [mul_div_cancel₀ _
        (ne_of_gt (show (0 : NNReal) < NNReal.mk C hC.le by exact hC)),
      ← NNReal.rpow_mul]
    have hp0 : p ≠ 0 := ne_of_gt hp
    have hmul : (1 / p) * p = 1 := by field_simp
    rw [hmul, NNReal.rpow_one]

@[simp] theorem scaledPower_apply (p C : ℝ) (hp : 0 < p) (hC : 0 < C)
    (n : NNReal) :
    scaledPower p C hp hC n = (NNReal.mk C hC.le * n) ^ p :=
  rfl

@[simp] theorem scaledPower_inverse (p C : ℝ) (hp : 0 < p) (hC : 0 < C)
    (t : NNReal) :
    (scaledPower p C hp hC).inverse t =
      t ^ (1 / p) / NNReal.mk C hC.le :=
  rfl

end RealTimeScale

/--
Levin's probability-weighted average-time cost.  This is the definition used
in TR1995 Example 4.1; it is distinct from RS93's stronger rank-only
characterization [`rankCost`] below.
-/
noncomputable def levinCost (d : Decider L) (μ : Subprobability)
    (T : RealTimeScale) : NNReal :=
  ∑' x, μ.prob x * T.inverse (d.actualRuntime x) / (max 1 x.length : Nat)

def IsLevinAverageTime (d : Decider L) (μ : Subprobability)
    (T : RealTimeScale) : Prop :=
  Summable
      (fun x => μ.prob x * T.inverse (d.actualRuntime x) /
        (max 1 x.length : Nat)) ∧
    levinCost d μ T ≤ 1

/--
RS93 rank-truncated cost:
`Σ_{rank μ x ≤ l} T⁻¹(runtime(x)) / max(1, |x|)`.
Zero-mass strings are omitted because their rank is defined to be zero.
-/
noncomputable def rankCost (d : Decider L) (μ : Subprobability)
    (T : TimeScale) (l : Nat) : NNReal :=
  ∑' x, if μ.prob x ≠ 0 ∧ μ.rank x ≤ l
    then (T.inverse (d.actualRuntime x) : NNReal) / (max 1 x.length : Nat)
    else 0

def IsAverageTime (d : Decider L) (μ : Subprobability) (T : TimeScale) : Prop :=
  ∀ l, 1 ≤ l → rankCost d μ T l ≤ l

def InAverageP (p : DistributionalProblem) : Prop :=
  ∃ d : Decider p.language, ∃ T : TimeScale,
    IsPolynomial T.toFun ∧ IsAverageTime d p.distribution T

end AvgCaseMls.Foundation
