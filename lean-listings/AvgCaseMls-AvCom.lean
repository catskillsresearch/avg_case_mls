/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Average-case complexity definitions (Reischuk-Schindelhauer framework).

Extracted from [`arxiv.md`](../arxiv.md) S5.

**Phase 1A:** `Bitstring`, `len`, `Distribution`, `DistributionalProblem`, `IsPolynomial`.

**Phase 1B:** `rank`, `T_inv`.

**Phase 1C:** `IsAvTime`, `DistTime`, `AvDTime`, rankability predicates.

**Phase 1D:** `AvP`, `InDistNP`, `DistributionalReduction`, `IsNPAverageComplete`.

**Phase 2+:** MLS hardness - proofs open in later modules.
-/

open Finset

namespace AvCom

/-! ## Phase 1A - inputs, distributions, POL -/

/-- Binary inputs $x \in \\{0,1\\}^*$ (TR1995-711 S3.2). -/
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
  have : 1 <= lenBot s := le_max_left 1 s.length
  omega

/--
A **finite-support** probability distribution on bitstrings.

Literature: $\\mu : \\Sigma^* \\to [0,1]$ with $\\sum_x \\mu(x) \\le 1$.
We restrict to an explicit finite `support` so rank and testing are well-defined (Phase 1B).
-/
structure Distribution where
  support : Finset Bitstring
  prob : Bitstring -> Real
  prob_nonneg : forall s, 0 <= prob s
  prob_zero_outside : forall s, s notin support -> prob s = 0
  prob_sum_le_one : support.sum prob <= 1

namespace Distribution

/-- Total mass on the declared support. -/
noncomputable def mass (mu : Distribution) : Real :=
  mu.support.sum mu.prob

theorem mass_le_one (mu : Distribution) : mu.mass <= 1 :=
  mu.prob_sum_le_one

end Distribution

noncomputable def pointMassProb (x : Bitstring) (p : Real) (s : Bitstring) : Real :=
  if s = x then p else 0

noncomputable def uniformProb (S : Finset Bitstring) (s : Bitstring) : Real :=
  if s in S then 1 / (S.card : Real) else 0

/-- Point mass $p$ on a single string (requires $0 \\le p \\le 1$). -/
noncomputable def pointMass (x : Bitstring) (p : Real)
    (hp0 : 0 <= p) (hp1 : p <= 1) : Distribution where
  support := {x}
  prob := pointMassProb x p
  prob_nonneg s := by
    unfold pointMassProb
    split_ifs with h
    * exact hp0
    * exact le_rfl
  prob_zero_outside s hs := by
    unfold pointMassProb
    by_cases h : s = x
    * exfalso
      exact hs (mem_singleton.mpr h)
    * simp [h]
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
    * exact div_nonneg zero_le_one (Nat.cast_nonneg S.card)
    * exact le_rfl
  prob_zero_outside s hs := by
    unfold uniformProb
    by_cases hmem : s in S
    * exfalso
      exact hs hmem
    * simp [hmem]
  prob_sum_le_one := by
    have hcard0 : (0 : Real) < S.card :=
      Nat.cast_pos.mpr (card_pos.mpr h)
    have hsum : (S.sum (uniformProb S) : Real) = S.sum fun _ => 1 / (S.card : Real) :=
      sum_congr rfl fun s hs => by simp [uniformProb, hs]
    calc
      (S.sum (uniformProb S) : Real) = S.sum fun _ => 1 / (S.card : Real) := hsum
      _ = (S.card : Real) * (1 / (S.card : Real)) := by rw [sum_const, nsmul_eq_mul]
      _ = 1 := by
        have hne : (S.card : Real) /= 0 := Nat.cast_ne_zero.mpr (card_pos.mpr h).ne'
        field_simp [hne]
      _ <= 1 := le_rfl

theorem uniformOn_mass (S : Finset Bitstring) (h : S.Nonempty) : (uniformOn S h).mass = 1 := by
  unfold Distribution.mass uniformOn
  have hsum : (S.sum (uniformProb S) : Real) = S.sum fun _ => 1 / (S.card : Real) :=
    sum_congr rfl fun s hs => by simp [uniformProb, hs]
  calc
    (S.sum (uniformProb S) : Real) = S.sum fun _ => 1 / (S.card : Real) := hsum
    _ = (S.card : Real) * (1 / (S.card : Real)) := by rw [sum_const, nsmul_eq_mul]
    _ = 1 := by
      have hne : (S.card : Real) /= 0 := Nat.cast_ne_zero.mpr (card_pos.mpr h).ne'
      field_simp [hne]

/--
A **distributional problem** $(L, \\mu)$: a language over bitstrings paired with a distribution.
-/
structure DistributionalProblem where
  L : Set Bitstring
  mu : Distribution

/--
**POL** (polynomial complexity bounds): $T(n) \\le c n^k + c$ for some constants $c, k$.
-/
def IsPolynomial (T : Nat -> Nat) : Prop :=
  exists c k : Nat, forall n, T n <= c * n ^ k + c

namespace IsPolynomial

theorem id : IsPolynomial id := <1, 1, fun n => by simp>

theorem const (c : Nat) : IsPolynomial (fun _ => c) := <c, 0, fun n => by simp>

theorem add_one (T : Nat -> Nat) (h : IsPolynomial T) : IsPolynomial fun n => T n + 1 := by
  obtain <c, k, hT> := h
  refine <c + 1, k, fun n => ?_>
  calc
    T n + 1 <= c * n ^ k + c + 1 := Nat.add_le_add_right (hT n) 1
    _ <= (c + 1) * n ^ k + (c + 1) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem add_const (T : Nat -> Nat) (d : Nat) (h : IsPolynomial T) :
    IsPolynomial fun n => T n + d := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
    simpa [Nat.add_assoc] using add_one (T := fun n => T n + d) ih

end IsPolynomial

/-! ## Phase 1B - rank and inverse bounds -/

/--
Rank of `x` under `mu`: count of support strings at least as probable as `x`.
When `mu.prob x = 0`, rank is `0` (RS93/TR1995-711 S3.2).

Counts only over `mu.support`; see [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/
noncomputable def rank (mu : Distribution) (x : Bitstring) : Nat :=
  if mu.prob x = 0 then 0
  else
    open Classical in
    (mu.support.filter (fun z => mu.prob x <= mu.prob z)).card

namespace rank

theorem zero (mu : Distribution) (x : Bitstring) (h : mu.prob x = 0) :
    rank mu x = 0 := by
  simp [rank, h]

theorem le_support_card (mu : Distribution) (x : Bitstring) :
    rank mu x <= mu.support.card := by
  unfold rank
  split_ifs with h
  * omega
  * exact card_filter_le _ _

end rank

/--
Generalized inverse: minimum `n` with `T n >= m`, found by search from `0`.

Partial: diverges if no such `n` exists (e.g. `T := fun _ => 0`, `m > 0`).
See [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/
partial def T_invAux (T : Nat -> Nat) (m n : Nat) : Nat :=
  if T n >= m then n else T_invAux T m (n + 1)

def T_inv (T : Nat -> Nat) (m : Nat) : Nat :=
  if m = 0 then 0 else T_invAux T m 0

namespace T_inv

theorem zero (T : Nat -> Nat) : T_inv T 0 = 0 := rfl

end T_inv

/-! ## Phase 1C - average time and dist-time classes -/

/-- Inputs whose rank under `mu` is at most `l`. -/
noncomputable def rankLe (mu : Distribution) (l : Nat) : Finset Bitstring :=
  mu.support.filter (fun x => rank mu x <= l)

theorem rankLe_mem {mu : Distribution} {l : Nat} {x : Bitstring} :
    x in rankLe mu l <-> x in mu.support /\ rank mu x <= l := by
  simp [rankLe, mem_filter]

/--
RS93 average-time condition (TR1995-711 S3.2): for all `l >= 1`,

`sum_{rank_mu(x) <= l} T-1(f(x)) / lenBot(x) <= l`.
-/
def IsAvTime (T : Nat -> Nat) (f : Bitstring -> Nat) (mu : Distribution) : Prop :=
  forall l : Nat, l >= 1 ->
    (rankLe mu l).sum (fun x => (T_inv T (f x) : Real) / (lenBot x : Real)) <= (l : Real)

/-- Notation matching the literature: `(f, mu) in Av(T)`. -/
abbrev IsAv (T : Nat -> Nat) (f : Bitstring -> Nat) (mu : Distribution) : Prop :=
  IsAvTime T f mu

namespace IsAvTime

theorem zero (T : Nat -> Nat) (mu : Distribution) : IsAvTime T (fun _ => 0) mu := by
  intro l hl
  have hterm : forall x in rankLe mu l, (T_inv T (0) : Real) / (lenBot x : Real) = 0 := by
    intro x hx
    rw [T_inv.zero]
    norm_cast
    exact zero_div _
  rw [sum_eq_zero hterm]
  norm_cast
  omega

end IsAvTime

/-- `mu` is `V`-rankable: `rank_mu(x) <= V(|x|)` for all `x`. -/
def IsTRankable (V : Nat -> Nat) (mu : Distribution) : Prop :=
  forall x, rank mu x <= V (len x)

/-- POL-rankable: bounded by some `V in POL` (polynomial-time rank computation deferred). -/
def IsPolRankable (mu : Distribution) : Prop :=
  exists V : Nat -> Nat, IsPolynomial V /\ IsTRankable V mu

namespace IsTRankable

theorem of_support (V : Nat -> Nat) (mu : Distribution)
    (h : forall x in mu.support, rank mu x <= V (len x)) :
    IsTRankable V mu := by
  intro x
  by_cases hx : x in mu.support
  * exact h x hx
  * have hr : rank mu x = 0 := rank.zero mu x (mu.prob_zero_outside x hx)
    rw [hr]
    exact Nat.zero_le _

end IsTRankable

/--
`DistTime T`: some running-time function witnesses `IsAvTime T f mu`.

We do not yet tie `f` to a decider for `L`; see [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/
def DistTime (T : Nat -> Nat) (prob : DistributionalProblem) : Prop :=
  exists f : Bitstring -> Nat, IsAvTime T f prob.mu

namespace IsPolRankable

theorem uniformOn_polRankable (S : Finset Bitstring) (h : S.Nonempty) :
    IsPolRankable (uniformOn S h) :=
  <fun _ => S.card, IsPolynomial.const S.card,
    IsTRankable.of_support _ _ fun x _ =>
      rank.le_support_card (uniformOn S h) x>

end IsPolRankable

namespace DistTime

theorem of_avTime {T : Nat -> Nat} {prob : DistributionalProblem} {f : Bitstring -> Nat}
    (h : IsAvTime T f prob.mu) : DistTime T prob :=
  <f, h>

theorem zero (T : Nat -> Nat) (prob : DistributionalProblem) : DistTime T prob :=
  of_avTime (IsAvTime.zero T prob.mu)

/-- Average-time witnesses depend only on the distribution, not the language label. -/
theorem same_mu {L L' : Set Bitstring} {mu : Distribution} {T : Nat -> Nat} :
    DistTime T <L, mu> <-> DistTime T <L', mu> :=
  Iff.rfl

end DistTime

/--
`AvDTime T V`: `DistTime T` on problems whose distribution is `V`-rankable.
Matches the report's `AvDTime(T, C)` with `C` instantiated as a rank bound.
-/
def AvDTime (T V : Nat -> Nat) (prob : DistributionalProblem) : Prop :=
  IsTRankable V prob.mu /\ DistTime T prob

namespace AvDTime

theorem of_distTime {T V : Nat -> Nat} {prob : DistributionalProblem}
    (hV : IsTRankable V prob.mu) (hT : DistTime T prob) : AvDTime T V prob :=
  <hV, hT>

end AvDTime

/-! ## Phase 1D - AvP, distNP, reductions, completeness -/

/--
Certificate-based NP membership (Phase **3A** fork): poly-sized witnesses plus a
`Bool` verifier. See [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/
def InNP (L : Set Bitstring) : Prop :=
  exists (verify : Bitstring -> Bitstring -> Bool) (bound : Nat -> Nat),
    IsPolynomial bound /\
    (forall x, x in L <-> exists cert, len cert <= bound (len x) /\ verify x cert = true)

namespace InNP

theorem intro {L : Set Bitstring} {verify : Bitstring -> Bitstring -> Bool} {bound : Nat -> Nat}
    (hbound : IsPolynomial bound)
    (h : forall x, x in L <-> exists cert, len cert <= bound (len x) /\ verify x cert = true) :
    InNP L :=
  <verify, bound, hbound, h>

theorem empty : InNP (empty : Set Bitstring) :=
  intro (verify := fun _ _ => false) (bound := fun _ => 0) (IsPolynomial.const 0) fun x => by
    simp

end InNP

/-- `distNP`: NP language plus POL-rankable distribution (TR1995-711 S3.2). -/
def InDistNP (prob : DistributionalProblem) : Prop :=
  InNP prob.L /\ IsPolRankable prob.mu

namespace InDistNP

theorem intro {prob : DistributionalProblem} (hNP : InNP prob.L) (hmu : IsPolRankable prob.mu) :
    InDistNP prob :=
  <hNP, hmu>

theorem uniformOn (L : Set Bitstring) (S : Finset Bitstring) (h : S.Nonempty)
    (hNP : InNP L) :
    InDistNP <L, uniformOn S h> :=
  intro hNP (IsPolRankable.uniformOn_polRankable S h)

end InDistNP

/--
Distributional reduction (TR1995-711 S3.2): map `f` with correctness `x in L_1 <-> f(x) in L_2`,
polynomial length growth `lenBot (f x) <= k_0 * lenBot(x)^{k_1}`, and domination

`rank_{mu_2}(f(x)) <= c_0 * lenBot(x)^{c_1} * rank_{mu_1}(x)`.
-/
def DistributionalReduction (source target : DistributionalProblem) : Prop :=
  exists f : Bitstring -> Bitstring,
    (forall x, x in source.L <-> f x in target.L) /\
    (exists k0 k1 : Nat, forall x, lenBot (f x) <= k0 * (lenBot x) ^ k1) /\
    (exists c0 c1 : Nat, 0 < c0 /\ 0 < c1 /\
      forall x, rank target.mu (f x) <= c0 * (lenBot x) ^ c1 * rank source.mu x)

namespace DistributionalReduction

theorem refl (p : DistributionalProblem) : DistributionalReduction p p := by
  refine <id, ?_, <1, 1, fun x => ?_>, <1, 1, one_pos, one_pos, fun x => ?_>>
  * intro x; simp
  * simp [lenBot, id_eq]
  * simp only [id_eq, pow_one, one_mul]
    rcases Nat.eq_zero_or_pos (rank p.mu x) with hr | hr
    * omega
    * exact Nat.le_mul_of_pos_left (rank p.mu x) (lenBot_ne_zero x)

private theorem compose_lenBound {f g : Bitstring -> Bitstring} {k0 k1 k0' k1' : Nat}
    (hf : forall x, lenBot (f x) <= k0 * (lenBot x) ^ k1)
    (hg : forall x, lenBot (g x) <= k0' * (lenBot x) ^ k1') :
    forall x, lenBot (g (f x)) <= k0' * k0 ^ k1' * (lenBot x) ^ (k1 * k1') := by
  intro x
  have hpow : (lenBot (f x)) ^ k1' <= (k0 * (lenBot x) ^ k1) ^ k1' := by
    cases k1' with
    | zero => simp
    | succ k => exact Nat.pow_le_pow_left (hf x) (k + 1)
  calc
    lenBot (g (f x)) <= k0' * (lenBot (f x)) ^ k1' := hg (f x)
    _ <= k0' * (k0 * (lenBot x) ^ k1) ^ k1' := Nat.mul_le_mul_left _ hpow
    _ = k0' * k0 ^ k1' * (lenBot x ^ k1) ^ k1' := by rw [Nat.mul_pow, <- Nat.mul_assoc]
    _ = k0' * k0 ^ k1' * lenBot x ^ (k1 * k1') := by rw [Nat.pow_mul]

private theorem compose_rankBound {p1 p2 p3 : DistributionalProblem} {f g : Bitstring -> Bitstring}
    {k0 k1 c0 c1 d0 d1 : Nat}
    (hf : forall x, lenBot (f x) <= k0 * (lenBot x) ^ k1)
    (hdom12 : forall x, rank p2.mu (f x) <= c0 * (lenBot x) ^ c1 * rank p1.mu x)
    (hdom23 : forall x, rank p3.mu (g x) <= d0 * (lenBot x) ^ d1 * rank p2.mu x) :
    forall x,
      rank p3.mu (g (f x)) <=
        d0 * c0 * k0 ^ d1 * (lenBot x) ^ (k1 * d1 + c1) * rank p1.mu x := by
  intro x
  have hpow : (lenBot (f x)) ^ d1 <= (k0 * (lenBot x) ^ k1) ^ d1 := by
    cases d1 with
    | zero => simp
    | succ d => exact Nat.pow_le_pow_left (hf x) (d + 1)
  calc
    rank p3.mu (g (f x)) <= d0 * (lenBot (f x)) ^ d1 * rank p2.mu (f x) := hdom23 (f x)
    _ <= d0 * (k0 * (lenBot x) ^ k1) ^ d1 * rank p2.mu (f x) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left d0 hpow)
    _ <= d0 * (k0 * (lenBot x) ^ k1) ^ d1 * (c0 * (lenBot x) ^ c1 * rank p1.mu x) :=
      Nat.mul_le_mul_left _ (hdom12 x)
    _ = d0 * c0 * k0 ^ d1 * (lenBot x) ^ (k1 * d1 + c1) * rank p1.mu x := by ring_nf

/--
Compose distributional reductions (TR1995-711 S3.2 transitivity).
-/
theorem trans {p1 p2 p3 : DistributionalProblem}
    (h12 : DistributionalReduction p1 p2) (h23 : DistributionalReduction p2 p3) :
    DistributionalReduction p1 p3 := by
  obtain <f, hf, hlenSpec, hdomSpec> := h12
  obtain <k0, k1, hlen12> := hlenSpec
  obtain <c0, c1, hc0, hc1, hdom12> := hdomSpec
  obtain <g, hg, hlenSpec', hdomSpec'> := h23
  obtain <k0', k1', hlen23> := hlenSpec'
  obtain <d0, d1, hd0, hd1, hdom23> := hdomSpec'
  refine
    <fun x => g (f x), ?_, <k0' * k0 ^ k1', k1 * k1', ?_>,
      <d0 * c0 * k0 ^ d1, k1 * d1 + c1, ?_, ?_, ?_>>
  * intro x; exact (hf x).trans (hg (f x))
  * intro x; exact compose_lenBound hlen12 hlen23 x
  * have hk0 : 0 < k0 := by
      by_contra hle
      simp only [not_lt] at hle
      have := hlen12 ([] : Bitstring)
      simp [lenBot] at this
      omega
    exact Nat.mul_pos (Nat.mul_pos hd0 hc0) (Nat.pow_pos hk0)
  * exact Nat.lt_of_lt_of_le hc1 (Nat.le_add_left _ _)
  * intro x; exact compose_rankBound hlen12 hdom12 hdom23 x

end DistributionalReduction

/--
Average polynomial time: POL-rankable distribution plus `DistTime T` for some `T in POL`.
Matches `DistTime(POL, POL-rankable)` in TR1995-711 S3.2.
-/
def AvP (prob : DistributionalProblem) : Prop :=
  IsPolRankable prob.mu /\ exists T : Nat -> Nat, IsPolynomial T /\ DistTime T prob

namespace AvP

theorem of_distTime {prob : DistributionalProblem} (hmu : IsPolRankable prob.mu)
    {T : Nat -> Nat} (hT : IsPolynomial T) (h : DistTime T prob) : AvP prob :=
  <hmu, T, hT, h>

theorem zero {prob : DistributionalProblem} (hmu : IsPolRankable prob.mu) {T : Nat -> Nat}
    (hT : IsPolynomial T) : AvP prob :=
  of_distTime hmu hT (DistTime.zero T prob)

/-- [`AvP`] depends on the distribution and time bounds, not the language label (see [`DistTime.same_mu`]). -/
theorem same_mu {L L' : Set Bitstring} {mu : Distribution} :
    AvP <L, mu> <-> AvP <L', mu> := by
  constructor <;> intro <hmu, T, hT, hDT> <;> exact <hmu, T, hT, by simpa [DistTime] using hDT>

end AvP

/-- NP-average (distNP) completeness: in `distNP` and hard for all of `distNP`. -/
def IsNPAverageComplete (target : DistributionalProblem) : Prop :=
  InDistNP target /\ forall source, InDistNP source -> DistributionalReduction source target

namespace IsNPAverageComplete

theorem intro {target : DistributionalProblem} (h : InDistNP target)
    (hred : forall source, InDistNP source -> DistributionalReduction source target) :
    IsNPAverageComplete target :=
  <h, hred>

/--
If `mid` is NP-average complete and `mid` reduces to `target`, then `target` is complete.
Corollary 5.1 pipeline: distNP-complete NBH core -> MLS target.
-/
theorem of_reductor {mid target : DistributionalProblem}
    (hTarget : InDistNP target) (hMid : IsNPAverageComplete mid)
    (hRed : DistributionalReduction mid target) :
    IsNPAverageComplete target :=
  intro hTarget fun source hsource =>
    DistributionalReduction.trans (hMid.2 source hsource) hRed

end IsNPAverageComplete

end AvCom
