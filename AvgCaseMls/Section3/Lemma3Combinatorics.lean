import AvgCaseMls.Section3.SDR

/-!
# Finite combinatorics used in CS87 Lemma 3
-/

namespace AvgCaseMls.Section3

namespace Hypergraph

/-- A division-free form of `choose n 2 = n(n-1)/2`. -/
theorem two_mul_choose_two (n : Nat) :
    2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd

/-- The pair-density inequality used in (5.1). -/
theorem choose_two_ratio_cross {s n : Nat} (hsn : s ≤ n) :
    n ^ 2 * s.choose 2 ≤ s ^ 2 * n.choose 2 := by
  by_cases hs0 : s = 0
  · simp [hs0]
  have hspos : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
  have hnpos : 1 ≤ n := hspos.trans hsn
  have hsR :
      (2 : ℝ) * s.choose 2 = s * (s - 1) := by
    exact_mod_cast two_mul_choose_two s
  have hnR :
      (2 : ℝ) * n.choose 2 = n * (n - 1) := by
    exact_mod_cast two_mul_choose_two n
  have hsnR : (s : ℝ) ≤ n := by exact_mod_cast hsn
  have hnonneg : 0 ≤ (s : ℝ) * n * (n - s) := by positivity
  have hgoal :
      (n : ℝ) ^ 2 * s.choose 2 ≤ (s : ℝ) ^ 2 * n.choose 2 := by
    nlinarith
  exact_mod_cast hgoal

/-- The number of `s`-sets containing a fixed two-set. -/
theorem card_ssets_containing_pair {n s : Nat} (p : Finset (Fin n))
    (hp : p.card = 2) (hs : 2 ≤ s) :
    ((Finset.univ.powersetCard s).filter fun S => p ⊆ S).card =
      (n - 2).choose (s - 2) := by
  classical
  let U : Finset (Fin n) := Finset.univ \ p
  let A := (Finset.univ.powersetCard s).filter fun S => p ⊆ S
  let B := U.powersetCard (s - 2)
  have hpU : p ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
  have hUcard : U.card = n - 2 := by
    rw [Finset.card_sdiff_of_subset hpU, Finset.card_univ,
      Fintype.card_fin, hp]
  have hcard : A.card = B.card := by
    apply Finset.card_bij (fun S _ => S \ p)
    · intro S hS
      simp only [A, Finset.mem_filter, Finset.mem_powersetCard] at hS
      rw [Finset.mem_powersetCard]
      constructor
      · exact Finset.sdiff_subset_sdiff hS.1.1 (Finset.Subset.rfl)
      · rw [Finset.card_sdiff_of_subset hS.2, hS.1.2, hp]
    · intro S₁ hS₁ S₂ hS₂ heq
      simp only [A, Finset.mem_filter, Finset.mem_powersetCard] at hS₁ hS₂
      apply Finset.Subset.antisymm
      · intro x hx
        by_cases hxp : x ∈ p
        · exact hS₂.2 hxp
        · have : x ∈ S₁ \ p := Finset.mem_sdiff.mpr ⟨hx, hxp⟩
          rw [heq] at this
          exact (Finset.mem_sdiff.mp this).1
      · intro x hx
        by_cases hxp : x ∈ p
        · exact hS₁.2 hxp
        · have : x ∈ S₂ \ p := Finset.mem_sdiff.mpr ⟨hx, hxp⟩
          rw [← heq] at this
          exact (Finset.mem_sdiff.mp this).1
    · intro T hT
      refine ⟨p ∪ T, ?_, ?_⟩
      · simp only [A, Finset.mem_filter, Finset.mem_powersetCard]
        simp only [B, Finset.mem_powersetCard] at hT
        have hdisj : Disjoint p T := by
          rw [Finset.disjoint_left]
          intro x hxp hxT
          exact (Finset.mem_sdiff.mp (hT.1 hxT)).2 hxp
        constructor
        · constructor
          · exact Finset.union_subset hpU
              (hT.1.trans Finset.sdiff_subset)
          · rw [Finset.card_union_of_disjoint hdisj, hp, hT.2]
            omega
        · exact Finset.subset_union_left
      · simp only [Finset.union_sdiff_left]
        simp only [B, Finset.mem_powersetCard] at hT
        have hdisj : Disjoint T p := by
          rw [Finset.disjoint_left]
          intro x hxT hxp
          exact (Finset.mem_sdiff.mp (hT.1 hxT)).2 hxp
        exact Finset.sdiff_eq_self_iff_disjoint.mpr hdisj
  rw [hcard, Finset.card_powersetCard, hUcard]

/-- Exact pair double-count: this is the combinatorial inequality preceding
CS87 (5.1), retaining edge-index multiplicity. -/
theorem sum_multiHitEdges_le
    (H : Hypergraph n m) (hk : H.IsKUniform k) (s : Nat) (hs : 2 ≤ s) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
        (Finset.univ.filter fun i =>
          2 ≤ (H.edge i ∩ S).card).card) ≤
      m * k.choose 2 * (n - 2).choose (s - 2) := by
  classical
  let Ω := (Finset.univ : Finset (Fin n)).powersetCard s
  have hpoint : ∀ S ∈ Ω,
      (Finset.univ.filter fun i =>
          2 ≤ (H.edge i ∩ S).card).card ≤
        ∑ i : Fin m, (H.edge i ∩ S).card.choose 2 := by
    intro S _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : 2 ≤ (H.edge i ∩ S).card
    · simp only [hi, if_true]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos hi))
    · simp [hi]
  calc
    (∑ S ∈ Ω, (Finset.univ.filter fun i =>
        2 ≤ (H.edge i ∩ S).card).card)
        ≤ ∑ S ∈ Ω, ∑ i : Fin m, (H.edge i ∩ S).card.choose 2 :=
      Finset.sum_le_sum fun S hS => hpoint S hS
    _ = ∑ i : Fin m, ∑ S ∈ Ω, (H.edge i ∩ S).card.choose 2 := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin m,
        (H.edge i).card.choose 2 * (n - 2).choose (s - 2) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ S ∈ Ω, (H.edge i ∩ S).card.choose 2) =
            ∑ S ∈ Ω, ((H.edge i ∩ S).powersetCard 2).card := by
              apply Finset.sum_congr rfl
              intro S _
              rw [Finset.card_powersetCard]
        _ = ∑ S ∈ Ω,
            (((H.edge i).powersetCard 2).filter (fun p => p ⊆ S)).card := by
              apply Finset.sum_congr rfl
              intro S _
              congr 1
              ext p
              simp only [Finset.mem_powersetCard, Finset.mem_filter]
              constructor
              · rintro ⟨hp, hpcard⟩
                exact ⟨⟨hp.trans Finset.inter_subset_left, hpcard⟩,
                  hp.trans Finset.inter_subset_right⟩
              · rintro ⟨⟨hpE, hpcard⟩, hpS⟩
                exact ⟨fun x hx => Finset.mem_inter.mpr ⟨hpE hx, hpS hx⟩,
                  hpcard⟩
        _ = ∑ p ∈ (H.edge i).powersetCard 2,
            (Ω.filter fun S => p ⊆ S).card := by
              simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
              rw [Finset.sum_comm]
        _ = ∑ _p ∈ (H.edge i).powersetCard 2,
            (n - 2).choose (s - 2) := by
              apply Finset.sum_congr rfl
              intro p hp
              rw [card_ssets_containing_pair p
                (Finset.mem_powersetCard.mp hp).2 hs]
        _ = (H.edge i).card.choose 2 * (n - 2).choose (s - 2) := by
              rw [← Finset.card_powersetCard]
              simp
    _ = ∑ _i : Fin m, k.choose 2 * (n - 2).choose (s - 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hk i]
    _ = m * k.choose 2 * (n - 2).choose (s - 2) := by simp [Nat.mul_assoc]

/-- Finite Markov inequality in the exact factor-two form used to define
normal sets in CS87. -/
theorem twice_card_le_of_above_twice_average
    {α : Type*} (Ω : Finset α) (f : α → Nat) :
    2 * ((Ω.filter fun x => 2 * (∑ y ∈ Ω, f y) < f x * Ω.card).card) ≤
      Ω.card := by
  classical
  let B := Ω.filter fun x => 2 * (∑ y ∈ Ω, f y) < f x * Ω.card
  by_cases hΩ : Ω.card = 0
  · simp [hΩ]
  have hsumB : B.card * (2 * ∑ y ∈ Ω, f y) <
      (∑ x ∈ B, f x) * Ω.card ∨ B = ∅ := by
    by_cases hB : B = ∅
    · exact Or.inr hB
    · left
      have hBne : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB
      have hpoint : ∀ x ∈ B,
          2 * (∑ y ∈ Ω, f y) < f x * Ω.card := by
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      calc
        B.card * (2 * ∑ y ∈ Ω, f y) =
            ∑ _x ∈ B, (2 * ∑ y ∈ Ω, f y) := by simp
        _ < ∑ x ∈ B, f x * Ω.card :=
          Finset.sum_lt_sum_of_nonempty hBne (fun x hx => hpoint x hx)
        _ = (∑ x ∈ B, f x) * Ω.card := by
          rw [Finset.sum_mul]
  by_cases hB : B = ∅
  · simp [B, hB]
  have hlt := hsumB.resolve_right hB
  have hsub : B ⊆ Ω := Finset.filter_subset _ _
  have hsumle : (∑ x ∈ B, f x) ≤ ∑ x ∈ Ω, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; omega)
  have hposΩ : 0 < Ω.card := Nat.pos_of_ne_zero hΩ
  have hsumpos : 0 < ∑ x ∈ Ω, f x := by
    by_contra hz
    have hz' : ∑ x ∈ Ω, f x = 0 := by omega
    have hpointzero : ∀ x ∈ Ω, f x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hz'
    have : B = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨x, hx⟩
      have hxΩ := (Finset.mem_filter.mp hx).1
      have hbad := (Finset.mem_filter.mp hx).2
      rw [hz', hpointzero x hxΩ] at hbad
      omega
    exact hB this
  have hmul : (2 * B.card) * (∑ x ∈ Ω, f x) <
      Ω.card * (∑ x ∈ Ω, f x) := by
    calc
      (2 * B.card) * (∑ x ∈ Ω, f x) =
          B.card * (2 * ∑ x ∈ Ω, f x) := by ring
      _ < (∑ x ∈ B, f x) * Ω.card := hlt
      _ ≤ (∑ x ∈ Ω, f x) * Ω.card := Nat.mul_le_mul_right _ hsumle
      _ = Ω.card * (∑ x ∈ Ω, f x) := Nat.mul_comm _ _
  have : 2 * B.card < Ω.card :=
    (Nat.mul_lt_mul_right hsumpos).mp (by simpa using hmul)
  exact Nat.le_of_lt this

/-- The elementary rearrangement from (5.7), (5.8), (5.1), and (5.5). -/
theorem deficiency_bound_of_cs87_equations
    {a barN p q j s k : ℝ}
    (h57 : (2 - a / 128) * j ≤ p + q)
    (h58 : p - 2 * k * barN ≤ j)
    (h51 : barN ≤ a * s / (128 * k))
    (h55 : j ≤ 2 * s)
    (ha : 0 ≤ a) (hk : 0 < k) :
    j - q ≤ a * s / 32 := by
  have hA : j - q ≤ p - (1 - a / 128) * j := by linarith
  have hB : p - (1 - a / 128) * j ≤
      2 * k * barN + (a / 128) * j := by linarith
  calc
    j - q ≤ 2 * k * barN + (a / 128) * j := hA.trans hB
    _ ≤ 2 * k * (a * s / (128 * k)) + (a / 128) * (2 * s) := by
      gcongr
    _ = a * s / 32 := by field_simp; ring

end Hypergraph

end AvgCaseMls.Section3
