/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Foundation.Rankability

namespace AvgCaseMls.Foundation

/-- A machine together with a proof that its executable runs decide `L`. -/
structure Decider (L : Set Bitstring) where
  machine : Machine
  halts : ∀ x, ∃ fuel r, eval machine fuel x = some r
  correct_run :
    ∀ x fuel r, eval machine fuel x = some r → (r.accept = true ↔ x ∈ L)

namespace Decider

theorem decides (d : Decider L) : Decides d.machine L := by
  intro x
  obtain ⟨fuel, r, hr⟩ := d.halts x
  exact ⟨r, ⟨fuel, hr⟩, d.correct_run x fuel r hr⟩

theorem terminates (d : Decider L) (x : Bitstring) :
    ∃ fuel r, eval d.machine fuel x = some r :=
  d.halts x

theorem eventually_isSome (d : Decider L) (x : Bitstring) :
    ∃ fuel, (eval d.machine fuel x).isSome = true := by
  obtain ⟨fuel, r, hr⟩ := d.terminates x
  exact ⟨fuel, by simp [hr]⟩

/-- Least fuel at which the executable evaluator returns a result. -/
noncomputable def haltingFuel (d : Decider L) (x : Bitstring) : Nat :=
  Nat.find (d.eventually_isSome x)

theorem haltingFuel_spec (d : Decider L) (x : Bitstring) :
    ∃ r, eval d.machine (d.haltingFuel x) x = some r := by
  have h := Nat.find_spec (d.eventually_isSome x)
  change (eval d.machine (d.haltingFuel x) x).isSome = true at h
  cases hopt : eval d.machine (d.haltingFuel x) x with
  | none =>
      simp only [hopt, Option.isSome_none] at h
      cases h
  | some r => exact ⟨r, rfl⟩

noncomputable def actualResult (d : Decider L) (x : Bitstring) : Result :=
  Classical.choose (d.haltingFuel_spec x)

theorem actualResult_spec (d : Decider L) (x : Bitstring) :
    eval d.machine (d.haltingFuel x) x = some (d.actualResult x) :=
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
