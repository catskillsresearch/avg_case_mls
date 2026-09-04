import AvgCaseMls.Section3.Projection
import AvgCaseMls.Section3.ResolutionCompleteness
import AvgCaseMls.Section3.Lemma5

/-!
# TR1995 Theorems 3.1 and 3.2

This module combines CS87 Lemmas 4 and 5 with the elementary
unsatisfiability estimate.  It also records the expectation argument yielding
the average resolution lower bound.
-/

namespace AvgCaseMls.Section3

open Filter

noncomputable def denseCNFPropertyPQEvent
    (c k : Nat) (a b : ℝ) (r : Nat) :
    Set (OrdinaryCNF (r + k) (c * (r + k)) k) :=
  denseProjectedEvent c k (Hypergraph.densePropertyPQEvent c k a b) r

noncomputable def denseTheorem31Event
    (c k : Nat) (ε : ℝ) (r : Nat) :
    Set (OrdinaryCNF (r + k) (c * (r + k)) k) :=
  {F | ¬ Satisfiable (eraseOrdinary F) ∧
    (1 + ε) ^ (r + k) ≤ resolutionComplexity (eraseOrdinary F)}

noncomputable def denseAverageResolutionComplexity (c k r : Nat) : ℝ :=
  (denseRandomCNF c k r).expectation fun F =>
    resolutionComplexity (eraseOrdinary F)

/-- Average resolution complexity under `K(c*n,n,k)`.  The value at the
finitely many infeasible sizes `n < k` is set to zero. -/
noncomputable def averageResolutionComplexity (c k n : Nat) : ℝ :=
  if h : k ≤ n then
    (randomCNFOfLE n (c * n) k h).expectation fun F =>
      resolutionComplexity (eraseOrdinary F)
  else 0

@[simp] theorem denseAverageResolutionComplexity_eq
    (c k r : Nat) :
    denseAverageResolutionComplexity c k r =
      averageResolutionComplexity c k (r + k) := by
  simp [denseAverageResolutionComplexity, denseRandomCNF,
    averageResolutionComplexity]

theorem dense_propertyPQ_withHighProbability
    (c k : Nat) (hc : 0 < c) (hk : 3 ≤ k) :
    WithHighProbability (denseRandomCNF c k)
      (denseCNFPropertyPQEvent c k
        (Hypergraph.cs87Lemma4A c k) (Hypergraph.cs87Lemma4B c k)) := by
  exact dense_projection_withHighProbability c k _
    (Hypergraph.cs87Lemma4_propertyPQ_withHighProbability c k hc hk)

private theorem cs87Lemma4B_le_one
    (c k : Nat) (hc : 0 < c) (hk : 3 ≤ k) :
    Hypergraph.cs87Lemma4B c k ≤ 1 := by
  have hk2 : 1 < k := by omega
  have hy := Hypergraph.cs87Lemma4_first_density hk
  have hy1pos : 0 < Hypergraph.cs87Lemma4Y₁ k := by
    simp [Hypergraph.cs87Lemma4Y₁]
    positivity
  have hy1le : Hypergraph.cs87Lemma4Y₁ k ≤ 1 := by
    simp only [Hypergraph.cs87Lemma4Y₁]
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hden : (0 : ℝ) < 2 * k + 1 := by positivity
    rw [div_le_one hden]
    linarith
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      convert Real.add_one_le_exp (1 : ℝ) using 1 <;> norm_num
    linarith
  have hden : (1 : ℝ) ≤ (c : ℝ) * Real.exp 1 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (c : ℝ) * Real.exp 1 :=
        mul_le_mul hcR he (by norm_num) (by positivity)
  have hratio :
      0 ≤ Hypergraph.cs87Lemma4Y₁ k / ((c : ℝ) * Real.exp 1) := by
    positivity
  have hratio1 :
      Hypergraph.cs87Lemma4Y₁ k / ((c : ℝ) * Real.exp 1) ≤ 1 :=
    (div_le_one (by positivity)).2 (hy1le.trans hden)
  have hpow :
      (Hypergraph.cs87Lemma4Y₁ k / ((c : ℝ) * Real.exp 1)) ^
          Hypergraph.cs87Lemma4Y₁ k ≤ 1 :=
    Real.rpow_le_one hratio hratio1 (le_of_lt hy1pos)
  have hfactor : (0 : ℝ) ≤ 1 / (2 * Real.exp 1) := by positivity
  have hfactor1 : (1 / (2 * Real.exp 1) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.add_one_le_exp 1]
  have hbase :
      0 ≤ (1 / (2 * Real.exp 1)) *
        (Hypergraph.cs87Lemma4Y₁ k / ((c : ℝ) * Real.exp 1)) ^
          Hypergraph.cs87Lemma4Y₁ k := mul_nonneg hfactor (by positivity)
  have hbase1 :
      (1 / (2 * Real.exp 1)) *
        (Hypergraph.cs87Lemma4Y₁ k / ((c : ℝ) * Real.exp 1)) ^
          Hypergraph.cs87Lemma4Y₁ k ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hfactor1 hpow (by positivity) (by norm_num)
      _ = 1 := one_mul 1
  have halpha :
      0 ≤ (cs87Alpha k (Hypergraph.cs87Lemma4Y₁ k))⁻¹ := by
    exact inv_nonneg.mpr (cs87_alpha_pos hk2 hy).le
  have hx : cs87LocalSparsityX c k (Hypergraph.cs87Lemma4Y₁ k) ≤ 1 := by
    exact Real.rpow_le_one hbase hbase1 halpha
  have ha :
      Hypergraph.cs87Lemma4A c k ≤ 1 := by
    dsimp [Hypergraph.cs87Lemma4A, Hypergraph.cs87Lemma4XPrime]
    exact (div_le_one (by positivity)).2 (hx.trans (by exact_mod_cast hk2.le))
  calc
    Hypergraph.cs87Lemma4B c k ≤ Hypergraph.cs87Lemma4A c k / 8 :=
      (min_le_right _ _).trans (min_le_right _ _)
    _ ≤ 1 := by nlinarith

private theorem eventually_lemma5_exceeds_exponential
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ r : Nat in atTop,
        (1 + ε) ^ r ≤
          (1 / 4 : ℝ) *
            (Real.exp 1 / 2) ^ (a * ⌊b * r⌋₊ / 16) := by
  let q : ℝ := Real.exp 1 / 2
  have hq : 1 < q := by
    dsimp [q]
    nlinarith [Real.exp_one_gt_d9]
  let B : ℝ := q ^ (a * b / 64)
  have hab : 0 < a * b / 64 := by positivity
  have hB : 1 < B := by
    dsimp [B]
    simpa using Real.one_lt_rpow hq hab
  let ε := B - 1
  refine ⟨ε, by dsimp [ε]; linarith, ?_⟩
  have hcast : Tendsto (fun r : Nat => (r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hbr : Tendsto (fun r : Nat => b * (r : ℝ)) atTop atTop :=
    hcast.const_mul_atTop hb
  have hlarge : ∀ᶠ r : Nat in atTop, (2 : ℝ) ≤ b * r :=
    hbr.eventually (eventually_ge_atTop 2)
  have hpowlarge : ∀ᶠ r : Nat in atTop, (4 : ℝ) ≤ B ^ r :=
    (tendsto_pow_atTop_atTop_of_one_lt hB).eventually
      (eventually_ge_atTop 4)
  filter_upwards [hlarge, hpowlarge] with r hr hBr
  have hfloor : b * (r : ℝ) / 2 ≤ (⌊b * r⌋₊ : ℝ) := by
    have hlt := Nat.lt_floor_add_one (b * (r : ℝ))
    nlinarith
  have hexp :
      a * b * (r : ℝ) / 32 ≤ a * (⌊b * r⌋₊ : ℝ) / 16 := by
    nlinarith
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq.le
  have hmono :
      q ^ (a * b * (r : ℝ) / 32) ≤
        q ^ (a * (⌊b * r⌋₊ : ℝ) / 16) :=
    Real.rpow_le_rpow_of_exponent_le hq.le hexp
  have hBpow :
      B ^ r = q ^ (a * b * (r : ℝ) / 64) := by
    dsimp [B]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hq0]
    congr 1
    ring
  have hdouble :
      q ^ (a * b * (r : ℝ) / 32) = (B ^ r) ^ 2 := by
    rw [hBpow, ← Real.rpow_two, ← Real.rpow_mul hq0]
    congr 1
    ring
  dsimp [ε]
  rw [show 1 + (B - 1) = B by ring]
  change B ^ r ≤
    (1 / 4 : ℝ) * q ^ (a * (⌊b * r⌋₊ : ℝ) / 16)
  calc
    B ^ r ≤ (1 / 4 : ℝ) * (B ^ r) ^ 2 := by nlinarith
    _ = (1 / 4 : ℝ) * q ^ (a * b * (r : ℝ) / 32) := by rw [hdouble]
    _ ≤ _ := by gcongr

theorem theorem31_with_explicit_constants
    (c k : Nat) (hc : 0 < c) (hk : 3 ≤ k)
    (hdensity : (7 / 10 : ℝ) ≤
      (c : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) :
    ∃ ε : ℝ, 0 < ε ∧
      WithHighProbability (denseRandomCNF c k)
        (denseTheorem31Event c k ε) := by
  let a := Hypergraph.cs87Lemma4A c k
  let b := Hypergraph.cs87Lemma4B c k
  have ha : 0 < a := by
    dsimp [a, Hypergraph.cs87Lemma4A, Hypergraph.cs87Lemma4XPrime]
    exact div_pos
      (cs87_localSparsityX_pos hc (by omega)
        (Hypergraph.cs87Lemma4_first_density hk)) (by positivity)
  have hb : 0 < b := by
    dsimp [b, Hypergraph.cs87Lemma4B]
    have hx : 0 < Hypergraph.cs87Lemma4X c k :=
      cs87_localSparsityX_pos hc (by omega)
        (Hypergraph.cs87Lemma4_second_density c k hc hk)
    positivity
  rcases eventually_lemma5_exceeds_exponential ha hb with
    ⟨ε, hε, hnumeric⟩
  have hnumericShift : ∀ᶠ r : Nat in atTop,
      (1 + ε) ^ (r + k) ≤
        (1 / 4 : ℝ) *
          (Real.exp 1 / 2) ^
            (a * ⌊b * ((r + k : Nat) : ℝ)⌋₊ / 16) := by
    rw [eventually_atTop] at hnumeric ⊢
    rcases hnumeric with ⟨N, hN⟩
    exact ⟨N, fun r hr => hN (r + k)
      (hr.trans (Nat.le_add_right r k))⟩
  refine ⟨ε, hε, ?_⟩
  let hard := fun r =>
    denseUnsatisfiableEvent c k r ∩ denseCNFPropertyPQEvent c k a b r
  have hhard : WithHighProbability (denseRandomCNF c k) hard := by
    apply withHighProbability_inter
    · exact random_cnf_unsatisfiable_withHighProbability hk hdensity
    · exact dense_propertyPQ_withHighProbability c k hc hk
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hhard (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ))
      atTop (nhds 1))
  · filter_upwards [hnumericShift] with r hnum
    apply FinitePMF.eventProb_mono
    intro F hF
    rcases hF with ⟨hunsat, hPQ⟩
    have hunsat' : ¬Satisfiable (eraseOrdinary F) := by
      simpa [denseUnsatisfiableEvent, denseSatisfiableEvent,
        satisfiableEvent] using hunsat
    change (unsignedProjection F).toHypergraph.HasPropertyP a ∧
      (unsignedProjection F).toHypergraph.HasPropertyQ a b at hPQ
    have href : ∃ cs, ResolutionRefutation (eraseOrdinary F) cs :=
      resolution_complete (fun i => (F i).lits_isOrdinary.2) hunsat'
    have hlower := cs87_lemma5
      (eraseOrdinary_basedOn_projection F) hPQ.1 hPQ.2
      ha.le hb.le (cs87Lemma4B_le_one c k hc hk)
      ((min_le_right _ _).trans (min_le_right _ _)) href
    exact ⟨hunsat', hnum.trans hlower⟩
  · exact Filter.Eventually.of_forall fun r =>
      (denseRandomCNF c k r).eventProb_le_one _

private theorem expectation_ge_event_threshold
    {α : Type*} [Fintype α] (μ : FinitePMF α)
    (X : α → Nat) (E : Set α) (t : ℝ)
    (hX : ∀ x ∈ E, t ≤ X x) (ht : 0 ≤ t) :
    t * μ.eventProb E ≤ μ.expectation fun x => X x := by
  classical
  rw [FinitePMF.expectation, FinitePMF.eventProb]
  calc
    t * ∑ x ∈ Finset.univ.filter (· ∈ E), μ.prob x =
        ∑ x ∈ Finset.univ.filter (· ∈ E), μ.prob x * t := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ ≤ ∑ x ∈ Finset.univ.filter (· ∈ E), μ.prob x * X x := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (hX x (Finset.mem_filter.mp hx).2) (μ.prob_nonneg x)
    _ ≤ ∑ x, μ.prob x * X x := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro x _ _
      exact mul_nonneg (μ.prob_nonneg x) (Nat.cast_nonneg _)

theorem dense_average_resolution_omega
    (c k : Nat) (hc : 0 < c) (hk : 3 ≤ k)
    (hdensity : (7 / 10 : ℝ) ≤
      (c : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) :
    ∃ ε : ℝ, 0 < ε ∧
      IsAsymptoticOmega (denseAverageResolutionComplexity c k)
        (fun r => (1 + ε) ^ (r + k)) := by
  rcases theorem31_with_explicit_constants c k hc hk hdensity with
    ⟨ε, hε, hwhp⟩
  refine ⟨ε, hε, 1 / 2, by norm_num, ?_⟩
  have hhalf : ∀ᶠ r : Nat in atTop,
      (1 / 2 : ℝ) ≤
        (denseRandomCNF c k r).eventProb (denseTheorem31Event c k ε r) :=
    by
      filter_upwards [hwhp.eventually
        (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with r hr
      exact hr.le
  filter_upwards [hhalf] with r hr
  have ht : 0 ≤ (1 + ε) ^ (r + k) := by positivity
  calc
    (1 / 2 : ℝ) * (1 + ε) ^ (r + k) ≤
        (1 + ε) ^ (r + k) *
          (denseRandomCNF c k r).eventProb
            (denseTheorem31Event c k ε r) := by
          nlinarith
    _ ≤ denseAverageResolutionComplexity c k r := by
      exact expectation_ge_event_threshold _ _ _ _
        (fun F hF => hF.2) ht

theorem average_resolution_omega
    (c k : Nat) (hc : 0 < c) (hk : 3 ≤ k)
    (hdensity : (7 / 10 : ℝ) ≤
      (c : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) :
    ∃ ε : ℝ, 0 < ε ∧
      IsAsymptoticOmega (averageResolutionComplexity c k)
        (fun n => (1 + ε) ^ n) := by
  rcases dense_average_resolution_omega c k hc hk hdensity with
    ⟨ε, hε, d, hd, hdense⟩
  refine ⟨ε, hε, d, hd, ?_⟩
  rw [eventually_atTop] at hdense ⊢
  rcases hdense with ⟨N, hN⟩
  refine ⟨N + k, fun n hn => ?_⟩
  have hkn : k ≤ n := by omega
  have hr : N ≤ n - k := by omega
  have hbound := hN (n - k) hr
  have hne : n - k + k = n := Nat.sub_add_cancel hkn
  have havg :
      denseAverageResolutionComplexity c k (n - k) =
        averageResolutionComplexity c k n := by
    calc
      denseAverageResolutionComplexity c k (n - k) =
          averageResolutionComplexity c k (n - k + k) := by simp
      _ = averageResolutionComplexity c k n := congrArg _ hne
  change d * (1 + ε) ^ (n - k + k) ≤
    denseAverageResolutionComplexity c k (n - k) at hbound
  rw [hne] at hbound
  rw [havg] at hbound
  exact hbound

end AvgCaseMls.Section3

namespace TR1995

open AvgCaseMls.Section3

/-- **TR1995, Theorem 3.1.** Dense random ordinary `k`-CNFs are
unsatisfiable and require exponentially long resolution refutations with high
probability. -/
theorem theorem_3_1
    (c k : Nat) (hc : 0 < c) (hk : 3 ≤ k)
    (hdensity : (7 / 10 : ℝ) ≤
      (c : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) :
    ∃ ε : ℝ, 0 < ε ∧
      WithHighProbability (denseRandomCNF c k)
        (denseTheorem31Event c k ε) :=
  theorem31_with_explicit_constants c k hc hk hdensity

/-- **TR1995, Theorem 3.2.** Average resolution complexity in
`K(c n,n,k)` has an exponential asymptotic lower bound. -/
theorem theorem_3_2
    (c k : Nat) (hc : 0 < c) (hk : 3 ≤ k)
    (hdensity : (7 / 10 : ℝ) ≤
      (c : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) :
    ∃ ε : ℝ, 0 < ε ∧
      IsAsymptoticOmega (averageResolutionComplexity c k)
        (fun r => (1 + ε) ^ r) :=
  average_resolution_omega c k hc hk hdensity

end TR1995
