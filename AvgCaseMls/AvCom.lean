/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp

/-!
Average-case complexity definitions (Reischuk–Schindelhauer framework).

Extracted from [`arxiv.md`](../arxiv.md) §5.

**Phase 1A:** `Bitstring`, `len`, `Distribution`, `DistributionalProblem`, `IsPolynomial`.

**Phase 1B:** `rank`, `T_inv`.

**Phase 1C:** `IsAvTime`, `DistTime`, `AvDTime`, rankability predicates.

**Phase 1D:** `AvP`, `InDistNP`, `DistributionalReduction`, `IsNPAverageComplete`.

**Phase 2+:** MLS hardness — proofs open in later modules.
-/

open Finset

namespace AvCom

/-! ## Phase 1A — inputs, distributions, POL -/

/-- Binary inputs $x \in \\{0,1\\}^*$ (TR1995-711 §3.2). -/
abbrev Bitstring := List Bool

/-- Length $|x|$ as `List.length`. -/
def len (s : Bitstring) : Nat := s.length

@[simp] theorem len_eq (s : Bitstring) : len s = s.length := rfl

/--
Length used in RS93 denominators: `max 1 |x|` so the empty string is guarded.
See `DEFINITION_FORKS.md`.
-/
def lenBot (s : Bitstring) : Nat := max 1 s.length

theorem lenBot_empty : lenBot ([] : Bitstring) = 1 := rfl

theorem lenBot_ne_zero (s : Bitstring) : 0 < lenBot s := by
  have : 1 ≤ lenBot s := le_max_left 1 s.length
  omega

/--
A **finite-support** probability distribution on bitstrings.

Literature: $\\mu : \\Sigma^* \\to [0,1]$ with $\\sum_x \\mu(x) \\le 1$.
We restrict to an explicit finite `support` so rank and testing are well-defined (Phase 1B).
-/
structure Distribution where
  support : Finset Bitstring
  prob : Bitstring → Real
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_zero_outside : ∀ s, s ∉ support → prob s = 0
  prob_sum_le_one : support.sum prob ≤ 1

namespace Distribution

/-- Total mass on the declared support. -/
noncomputable def mass (μ : Distribution) : Real :=
  μ.support.sum μ.prob

theorem mass_le_one (μ : Distribution) : μ.mass ≤ 1 :=
  μ.prob_sum_le_one

end Distribution

noncomputable def pointMassProb (x : Bitstring) (p : Real) (s : Bitstring) : Real :=
  if s = x then p else 0

noncomputable def uniformProb (S : Finset Bitstring) (s : Bitstring) : Real :=
  if s ∈ S then 1 / (S.card : Real) else 0

/-- Point mass $p$ on a single string (requires $0 \\le p \\le 1$). -/
noncomputable def pointMass (x : Bitstring) (p : Real)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Distribution where
  support := {x}
  prob := pointMassProb x p
  prob_nonneg s := by
    unfold pointMassProb
    split_ifs with h
    · exact hp0
    · exact le_rfl
  prob_zero_outside s hs := by
    unfold pointMassProb
    by_cases h : s = x
    · exfalso
      exact hs (mem_singleton.mpr h)
    · simp [h]
  prob_sum_le_one := by
    rw [sum_singleton]
    simp only [pointMassProb]
    exact hp1

/-- Uniform distribution on a nonempty finite support. -/
noncomputable def uniformOn (S : Finset Bitstring) (h : S.Nonempty) : Distribution where
  support := S
  prob := uniformProb S
  prob_nonneg s := by
    unfold uniformProb
    split_ifs with hs
    · exact div_nonneg zero_le_one (Nat.cast_nonneg S.card)
    · exact le_rfl
  prob_zero_outside s hs := by
    unfold uniformProb
    by_cases hmem : s ∈ S
    · exfalso
      exact hs hmem
    · simp [hmem]
  prob_sum_le_one := by
    have hcard0 : (0 : Real) < S.card :=
      Nat.cast_pos.mpr (card_pos.mpr h)
    have hsum : (S.sum (uniformProb S) : Real) = S.sum fun _ => 1 / (S.card : Real) :=
      sum_congr rfl fun s hs => by simp [uniformProb, hs]
    calc
      (S.sum (uniformProb S) : Real) = S.sum fun _ => 1 / (S.card : Real) := hsum
      _ = (S.card : Real) * (1 / (S.card : Real)) := by rw [sum_const, nsmul_eq_mul]
      _ = 1 := by
        have hne : (S.card : Real) ≠ 0 := Nat.cast_ne_zero.mpr (card_pos.mpr h).ne'
        field_simp [hne]
      _ ≤ 1 := le_rfl

theorem uniformOn_mass (S : Finset Bitstring) (h : S.Nonempty) : (uniformOn S h).mass = 1 := by
  unfold Distribution.mass uniformOn
  have hsum : (S.sum (uniformProb S) : Real) = S.sum fun _ => 1 / (S.card : Real) :=
    sum_congr rfl fun s hs => by simp [uniformProb, hs]
  calc
    (S.sum (uniformProb S) : Real) = S.sum fun _ => 1 / (S.card : Real) := hsum
    _ = (S.card : Real) * (1 / (S.card : Real)) := by rw [sum_const, nsmul_eq_mul]
    _ = 1 := by
      have hne : (S.card : Real) ≠ 0 := Nat.cast_ne_zero.mpr (card_pos.mpr h).ne'
      field_simp [hne]

/--
A **distributional problem** $(L, \\mu)$: a language over bitstrings paired with a distribution.
-/
structure DistributionalProblem where
  L : Set Bitstring
  μ : Distribution

/--
**POL** (polynomial complexity bounds): $T(n) \\le c n^k + c$ for some constants $c, k$.
-/
def IsPolynomial (T : Nat → Nat) : Prop :=
  ∃ c k : Nat, ∀ n, T n ≤ c * n ^ k + c

namespace IsPolynomial

theorem id : IsPolynomial id := ⟨1, 1, fun n => by simp⟩

theorem const (c : Nat) : IsPolynomial (fun _ => c) := ⟨c, 0, fun n => by simp⟩

theorem add_one (T : Nat → Nat) (h : IsPolynomial T) : IsPolynomial fun n => T n + 1 := by
  obtain ⟨c, k, hT⟩ := h
  refine ⟨c + 1, k, fun n => ?_⟩
  calc
    T n + 1 ≤ c * n ^ k + c + 1 := Nat.add_le_add_right (hT n) 1
    _ ≤ (c + 1) * n ^ k + (c + 1) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem add_const (T : Nat → Nat) (d : Nat) (h : IsPolynomial T) :
    IsPolynomial fun n => T n + d := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
    simpa [Nat.add_assoc] using add_one (T := fun n => T n + d) ih

end IsPolynomial

/-! ## Phase 1B — rank and inverse bounds -/

/--
Rank of `x` under `μ`: count of support strings at least as probable as `x`.
When `μ.prob x = 0`, rank is `0` (RS93/TR1995-711 §3.2).

Counts only over `μ.support`; see [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/
noncomputable def rank (μ : Distribution) (x : Bitstring) : Nat :=
  if μ.prob x = 0 then 0
  else
    open Classical in
    (μ.support.filter (fun z => μ.prob x ≤ μ.prob z)).card

namespace rank

theorem zero (μ : Distribution) (x : Bitstring) (h : μ.prob x = 0) :
    rank μ x = 0 := by
  simp [rank, h]

theorem le_support_card (μ : Distribution) (x : Bitstring) :
    rank μ x ≤ μ.support.card := by
  unfold rank
  split_ifs with h
  · omega
  · exact card_filter_le _ _

end rank

/--
Generalized inverse: minimum `n` with `T n ≥ m`, found by search from `0`.

Partial: diverges if no such `n` exists (e.g. `T := fun _ => 0`, `m > 0`).
See [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/
partial def T_invAux (T : Nat → Nat) (m n : Nat) : Nat :=
  if T n ≥ m then n else T_invAux T m (n + 1)

def T_inv (T : Nat → Nat) (m : Nat) : Nat :=
  if m = 0 then 0 else T_invAux T m 0

namespace T_inv

theorem zero (T : Nat → Nat) : T_inv T 0 = 0 := rfl

end T_inv

/-! ## Phase 1C — average time and dist-time classes -/

/-- Inputs whose rank under `μ` is at most `l`. -/
noncomputable def rankLe (μ : Distribution) (l : Nat) : Finset Bitstring :=
  μ.support.filter (fun x => rank μ x ≤ l)

theorem rankLe_mem {μ : Distribution} {l : Nat} {x : Bitstring} :
    x ∈ rankLe μ l ↔ x ∈ μ.support ∧ rank μ x ≤ l := by
  simp [rankLe, mem_filter]

/--
RS93 average-time condition (TR1995-711 §3.2): for all `l ≥ 1`,

`∑_{rank_μ(x) ≤ l} T⁻¹(f(x)) / lenBot(x) ≤ l`.
-/
def IsAvTime (T : Nat → Nat) (f : Bitstring → Nat) (μ : Distribution) : Prop :=
  ∀ l : Nat, l ≥ 1 →
    (rankLe μ l).sum (fun x => (T_inv T (f x) : Real) / (lenBot x : Real)) ≤ (l : Real)

/-- Notation matching the literature: `(f, μ) ∈ Av(T)`. -/
abbrev IsAv (T : Nat → Nat) (f : Bitstring → Nat) (μ : Distribution) : Prop :=
  IsAvTime T f μ

namespace IsAvTime

theorem zero (T : Nat → Nat) (μ : Distribution) : IsAvTime T (fun _ => 0) μ := by
  intro l hl
  have hterm : ∀ x ∈ rankLe μ l, (T_inv T (0) : Real) / (lenBot x : Real) = 0 := by
    intro x hx
    rw [T_inv.zero]
    norm_cast
    exact zero_div _
  rw [sum_eq_zero hterm]
  norm_cast
  omega

end IsAvTime

/-- `μ` is `V`-rankable: `rank_μ(x) ≤ V(|x|)` for all `x`. -/
def IsTRankable (V : Nat → Nat) (μ : Distribution) : Prop :=
  ∀ x, rank μ x ≤ V (len x)

/-- POL-rankable: bounded by some `V ∈ POL` (polynomial-time rank computation deferred). -/
def IsPolRankable (μ : Distribution) : Prop :=
  ∃ V : Nat → Nat, IsPolynomial V ∧ IsTRankable V μ

namespace IsTRankable

theorem of_support (V : Nat → Nat) (μ : Distribution)
    (h : ∀ x ∈ μ.support, rank μ x ≤ V (len x)) :
    IsTRankable V μ := by
  intro x
  by_cases hx : x ∈ μ.support
  · exact h x hx
  · have hr : rank μ x = 0 := rank.zero μ x (μ.prob_zero_outside x hx)
    rw [hr]
    exact Nat.zero_le _

end IsTRankable

/--
`DistTime T`: some running-time function witnesses `IsAvTime T f μ`.

We do not yet tie `f` to a decider for `L`; see [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/
def DistTime (T : Nat → Nat) (prob : DistributionalProblem) : Prop :=
  ∃ f : Bitstring → Nat, IsAvTime T f prob.μ

namespace IsPolRankable

theorem uniformOn_polRankable (S : Finset Bitstring) (h : S.Nonempty) :
    IsPolRankable (uniformOn S h) :=
  ⟨fun _ => S.card, IsPolynomial.const S.card,
    IsTRankable.of_support _ _ fun x _ =>
      rank.le_support_card (uniformOn S h) x⟩

end IsPolRankable

namespace DistTime

theorem of_avTime {T : Nat → Nat} {prob : DistributionalProblem} {f : Bitstring → Nat}
    (h : IsAvTime T f prob.μ) : DistTime T prob :=
  ⟨f, h⟩

theorem zero (T : Nat → Nat) (prob : DistributionalProblem) : DistTime T prob :=
  of_avTime (IsAvTime.zero T prob.μ)

end DistTime

/--
`AvDTime T V`: `DistTime T` on problems whose distribution is `V`-rankable.
Matches the report's `AvDTime(T, C)` with `C` instantiated as a rank bound.
-/
def AvDTime (T V : Nat → Nat) (prob : DistributionalProblem) : Prop :=
  IsTRankable V prob.μ ∧ DistTime T prob

namespace AvDTime

theorem of_distTime {T V : Nat → Nat} {prob : DistributionalProblem}
    (hV : IsTRankable V prob.μ) (hT : DistTime T prob) : AvDTime T V prob :=
  ⟨hV, hT⟩

end AvDTime

/-! ## Phase 1D — AvP, distNP, reductions, completeness -/

/--
Certificate-based NP membership (Phase **3A** fork): poly-sized witnesses plus a
`Bool` verifier. See [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/
def InNP (L : Set Bitstring) : Prop :=
  ∃ (verify : Bitstring → Bitstring → Bool) (bound : Nat → Nat),
    IsPolynomial bound ∧
    (∀ x, x ∈ L ↔ ∃ cert, len cert ≤ bound (len x) ∧ verify x cert = true)

namespace InNP

theorem intro {L : Set Bitstring} {verify : Bitstring → Bitstring → Bool} {bound : Nat → Nat}
    (hbound : IsPolynomial bound)
    (h : ∀ x, x ∈ L ↔ ∃ cert, len cert ≤ bound (len x) ∧ verify x cert = true) :
    InNP L :=
  ⟨verify, bound, hbound, h⟩

theorem empty : InNP (∅ : Set Bitstring) :=
  intro (verify := fun _ _ => false) (bound := fun _ => 0) (IsPolynomial.const 0) fun x => by
    simp

end InNP

/-- `distNP`: NP language plus POL-rankable distribution (TR1995-711 §3.2). -/
def InDistNP (prob : DistributionalProblem) : Prop :=
  InNP prob.L ∧ IsPolRankable prob.μ

namespace InDistNP

theorem intro {prob : DistributionalProblem} (hNP : InNP prob.L) (hμ : IsPolRankable prob.μ) :
    InDistNP prob :=
  ⟨hNP, hμ⟩

theorem uniformOn (L : Set Bitstring) (S : Finset Bitstring) (h : S.Nonempty)
    (hNP : InNP L) :
    InDistNP ⟨L, uniformOn S h⟩ :=
  intro hNP (IsPolRankable.uniformOn_polRankable S h)

end InDistNP

/--
Distributional reduction (TR1995-711 §3.2): polynomial-time map `f` (time check deferred),
correctness `x ∈ L₁ ↔ f(x) ∈ L₂`, and domination

`rank_{μ₂}(f(x)) ≤ c₀ · lenBot(x)^{c₁} · rank_{μ₁}(x)`.
-/
def DistributionalReduction (source target : DistributionalProblem) : Prop :=
  ∃ f : Bitstring → Bitstring,
    (∀ x, x ∈ source.L ↔ f x ∈ target.L) ∧
    (∃ c0 c1 : Nat, 0 < c0 ∧ 0 < c1 ∧
      ∀ x, rank target.μ (f x) ≤ c0 * (lenBot x) ^ c1 * rank source.μ x)

namespace DistributionalReduction

theorem refl (p : DistributionalProblem) : DistributionalReduction p p := by
  refine ⟨id, ?_, ⟨1, 1, one_pos, one_pos, fun x => ?_⟩⟩
  · intro x; simp
  · simp only [id_eq, pow_one, one_mul]
    rcases Nat.eq_zero_or_pos (rank p.μ x) with hr | hr
    · omega
    · exact Nat.le_mul_of_pos_left (rank p.μ x) (lenBot_ne_zero x)

end DistributionalReduction

/--
Average polynomial time: POL-rankable distribution plus `DistTime T` for some `T ∈ POL`.
Matches `DistTime(POL, POL-rankable)` in TR1995-711 §3.2.
-/
def AvP (prob : DistributionalProblem) : Prop :=
  IsPolRankable prob.μ ∧ ∃ T : Nat → Nat, IsPolynomial T ∧ DistTime T prob

namespace AvP

theorem of_distTime {prob : DistributionalProblem} (hμ : IsPolRankable prob.μ)
    {T : Nat → Nat} (hT : IsPolynomial T) (h : DistTime T prob) : AvP prob :=
  ⟨hμ, T, hT, h⟩

theorem zero {prob : DistributionalProblem} (hμ : IsPolRankable prob.μ) {T : Nat → Nat}
    (hT : IsPolynomial T) : AvP prob :=
  of_distTime hμ hT (DistTime.zero T prob)

end AvP

/-- NP-average (distNP) completeness: in `distNP` and hard for all of `distNP`. -/
def IsNPAverageComplete (target : DistributionalProblem) : Prop :=
  InDistNP target ∧ ∀ source, InDistNP source → DistributionalReduction source target

namespace IsNPAverageComplete

theorem intro {target : DistributionalProblem} (h : InDistNP target)
    (hred : ∀ source, InDistNP source → DistributionalReduction source target) :
    IsNPAverageComplete target :=
  ⟨h, hred⟩

end IsNPAverageComplete

end AvCom
