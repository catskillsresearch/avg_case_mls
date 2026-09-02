import AvgCaseMls.Section3.LocalSparsity
import AvgCaseMls.Section3.PropertyQ

/-!
# CS87 Lemma 4
-/

namespace AvgCaseMls.Section3

open Filter

namespace FinitePMF

theorem eventProb_mono {α : Type*} [Fintype α]
    (μ : FinitePMF α) {E F : Set α} (hEF : E ⊆ F) :
    μ.eventProb E ≤ μ.eventProb F := by
  classical
  unfold eventProb
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hEF hx
  · intro x _ _
    exact μ.prob_nonneg x

theorem eventProb_inter_lower {α : Type*} [Fintype α]
    (μ : FinitePMF α) (E F : Set α) :
    μ.eventProb E + μ.eventProb F - 1 ≤ μ.eventProb (E ∩ F) := by
  classical
  let e := Finset.univ.filter fun x => x ∈ E
  let f := Finset.univ.filter fun x => x ∈ F
  have hunion :
      Finset.univ.filter (fun x => x ∈ E ∨ x ∈ F) = e ∪ f := by
    ext x
    simp [e, f]
  have hinter :
      Finset.univ.filter (fun x => x ∈ E ∧ x ∈ F) = e ∩ f := by
    ext x
    simp [e, f]
  have hid := Finset.sum_union_inter (s₁ := e) (s₂ := f) (f := μ.prob)
  have hle := μ.eventProb_le_one (E ∪ F)
  unfold eventProb at hle ⊢
  have hle' : (∑ x ∈ e ∪ f, μ.prob x) ≤ 1 := by
    rw [← hunion]
    simpa only [Set.mem_union]
      using hle
  rw [show Finset.univ.filter (fun x => x ∈ E) = e by rfl,
    show Finset.univ.filter (fun x => x ∈ F) = f by rfl]
  simp only [Set.mem_inter_iff]
  rw [hinter]
  linarith

end FinitePMF

theorem withHighProbability_inter
    {Ω : Nat → Type*} [∀ r, Fintype (Ω r)]
    (μ : ∀ r, FinitePMF (Ω r))
    (E F : ∀ r, Set (Ω r))
    (hE : WithHighProbability μ E)
    (hF : WithHighProbability μ F) :
    WithHighProbability μ (fun r => E r ∩ F r) := by
  have hlower :
      Tendsto (fun r => (μ r).eventProb (E r) +
        (μ r).eventProb (F r) - 1) atTop (nhds 1) := by
    simpa using (hE.add hF).sub
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ))
        atTop (nhds 1))
  have hupper : Tendsto (fun _r : Nat => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · exact Filter.Eventually.of_forall fun r =>
      (μ r).eventProb_inter_lower (E r) (F r)
  · exact Filter.Eventually.of_forall fun r =>
      (μ r).eventProb_le_one (E r ∩ F r)

namespace Hypergraph

noncomputable def cs87Lemma4Y₁ (k : Nat) : ℝ := 4 / (2 * k + 1)

noncomputable def cs87Lemma4XPrime (c k : Nat) : ℝ :=
  cs87LocalSparsityX c k (cs87Lemma4Y₁ k)

noncomputable def cs87Lemma4A (c k : Nat) : ℝ :=
  cs87Lemma4XPrime c k / k

noncomputable def cs87Lemma4Y₂ (c k : Nat) : ℝ :=
  1 / 2 + cs87Lemma4A c k / 512

noncomputable def cs87Lemma4X (c k : Nat) : ℝ :=
  cs87LocalSparsityX c k (cs87Lemma4Y₂ c k)

noncomputable def cs87Lemma4B (c k : Nat) : ℝ :=
  min (cs87Lemma4X c k / (2 * k))
    (min (cs87Lemma4A c k / (64 * c * k ^ 3))
      (cs87Lemma4A c k / 8))

noncomputable def densePropertyPQEvent (c k : Nat) (a b : ℝ) (r : Nat) :
    Set (OrderedKUniformHypergraph (r + k) (c * (r + k)) k) :=
  {G | G.toHypergraph.HasPropertyP a ∧ G.toHypergraph.HasPropertyQ a b}

noncomputable def cs87Lemma4JointSparseEvent (c k : Nat) (r : Nat) :
    Set (OrderedKUniformHypergraph (r + k) (c * (r + k)) k) :=
  denseSparseEvent c k (cs87Lemma4XPrime c k) (cs87Lemma4Y₁ k) r ∩
    denseSparseEvent c k (cs87Lemma4X c k) (cs87Lemma4Y₂ c k) r

theorem cs87Lemma4_first_density
    (hk : 3 ≤ k) :
    1 < ((k - 1 : Nat) : ℝ) * cs87Lemma4Y₁ k := by
  simp only [cs87Lemma4Y₁]
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < 2 * k + 1 := by positivity
  rw [show ((k - 1 : Nat) : ℝ) * (4 / (2 * k + 1)) =
    (4 * ((k - 1 : Nat) : ℝ)) / (2 * k + 1) by ring]
  rw [lt_div_iff₀ hden]
  rw [Nat.cast_sub (by omega : 1 ≤ k)]
  norm_num
  nlinarith

theorem cs87Lemma4_second_density
    (c k : Nat) (hc : 0 < c) (hk : 3 ≤ k) :
    1 < ((k - 1 : Nat) : ℝ) * cs87Lemma4Y₂ c k := by
  have hk2 : 1 < k := lt_of_lt_of_le (by omega) hk
  have hx' : 0 < cs87Lemma4XPrime c k :=
    cs87_localSparsityX_pos hc hk2 (cs87Lemma4_first_density hk)
  have ha : 0 < cs87Lemma4A c k := by
    exact div_pos hx' (by positivity)
  simp only [cs87Lemma4Y₂]
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Nat.cast_sub (by omega : 1 ≤ k)]
  norm_num
  nlinarith

theorem cs87Lemma4_joint_sparsity_withHighProbability
    (c k : Nat) (hc : 0 < c) (hk : 3 ≤ k) :
    WithHighProbability (denseRandomHypergraph c k)
      (cs87Lemma4JointSparseEvent c k) := by
  apply withHighProbability_inter
  · exact cs87_local_sparsity_withHighProbability hc (by omega)
      (cs87Lemma4_first_density hk)
  · exact cs87_local_sparsity_withHighProbability hc (by omega)
      (cs87Lemma4_second_density c k hc hk)

theorem cs87Lemma4_joint_event_subset_propertyPQ
    (c k r : Nat) (hc : 0 < c) (hk : 3 ≤ k) :
    cs87Lemma4JointSparseEvent c k r ⊆
      densePropertyPQEvent c k (cs87Lemma4A c k) (cs87Lemma4B c k) r := by
  intro G hG
  rcases hG with ⟨hsp₁, hsp₂⟩
  have hsparse₁ :
      G.toHypergraph.IsSparse
        (cs87Lemma4A c k * k) (4 / (2 * k + 1 : ℝ)) := by
    have hmem :
        G ∈ denseSparseEvent c k (cs87Lemma4XPrime c k)
          (cs87Lemma4Y₁ k) r := hsp₁
    simp only [denseSparseEvent, denseNonSparseEvent, Set.mem_compl_iff,
      nonSparseEvent, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hmem
    have hkR0 : (k : ℝ) ≠ 0 := by positivity
    simpa [cs87Lemma4A, cs87Lemma4Y₁, div_mul_cancel₀ _ hkR0] using hmem
  have hsparse₂ :
      G.toHypergraph.IsSparse (cs87Lemma4X c k)
        (1 / 2 + cs87Lemma4A c k / 512) := by
    have hmem :
        G ∈ denseSparseEvent c k (cs87Lemma4X c k)
          (cs87Lemma4Y₂ c k) r := hsp₂
    simp only [denseSparseEvent, denseNonSparseEvent, Set.mem_compl_iff,
      nonSparseEvent, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hmem
    simpa [cs87Lemma4Y₂] using hmem
  have hk2 : 1 < k := lt_of_lt_of_le (by omega) hk
  have hx' : 0 < cs87Lemma4XPrime c k :=
    cs87_localSparsityX_pos hc hk2 (cs87Lemma4_first_density hk)
  have ha : 0 < cs87Lemma4A c k :=
    div_pos hx' (by positivity)
  have hx : 0 < cs87Lemma4X c k :=
    cs87_localSparsityX_pos hc hk2 (cs87Lemma4_second_density c k hc hk)
  have hQ := G.toHypergraph.propertyQ_of_sparse
    G.toHypergraph_isKUniform (by omega) hc ha (le_of_lt hx)
      hsparse₁ hsparse₂
  exact ⟨G.toHypergraph.propertyP_of_sparse
    G.toHypergraph_isKUniform hsparse₁, by
      simpa [cs87Lemma4B] using hQ⟩

theorem cs87Lemma4_propertyPQ_withHighProbability
    (c k : Nat) (hc : 0 < c) (hk : 3 ≤ k) :
    WithHighProbability (denseRandomHypergraph c k)
      (densePropertyPQEvent c k (cs87Lemma4A c k) (cs87Lemma4B c k)) := by
  have hjoint := cs87Lemma4_joint_sparsity_withHighProbability c k hc hk
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hjoint (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ))
      atTop (nhds 1))
  · exact Filter.Eventually.of_forall fun r => by
      unfold cs87Lemma4JointSparseEvent densePropertyPQEvent at *
      apply FinitePMF.eventProb_mono
      exact cs87Lemma4_joint_event_subset_propertyPQ c k r hc hk
  · exact Filter.Eventually.of_forall fun r =>
      (denseRandomHypergraph c k r).eventProb_le_one _

/-- CS87 Lemma 4 with its source quantifiers and `b ≤ a/8`. -/
theorem cs87_lemma4 (c k : Nat) (hc : 0 < c) (hk : 3 ≤ k) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ b ≤ a / 8 ∧
      WithHighProbability (denseRandomHypergraph c k)
        (densePropertyPQEvent c k a b) := by
  refine ⟨cs87Lemma4A c k, cs87Lemma4B c k, ?_, ?_, ?_, ?_⟩
  · have hk2 : 1 < k := by omega
    exact div_pos
      (cs87_localSparsityX_pos hc hk2 (cs87Lemma4_first_density hk))
      (by positivity)
  · dsimp [cs87Lemma4B]
    have hk2 : 1 < k := by omega
    have ha : 0 < cs87Lemma4A c k := div_pos
      (cs87_localSparsityX_pos hc hk2 (cs87Lemma4_first_density hk))
      (by positivity)
    have hx : 0 < cs87Lemma4X c k :=
      cs87_localSparsityX_pos hc hk2 (cs87Lemma4_second_density c k hc hk)
    positivity
  · exact (min_le_right _ _).trans (min_le_right _ _)
  · exact cs87Lemma4_propertyPQ_withHighProbability c k hc hk

end Hypergraph

end AvgCaseMls.Section3
