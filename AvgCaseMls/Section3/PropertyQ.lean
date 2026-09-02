/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Section3.Lemma3Combinatorics

/-!
# Deterministic cluster machinery for CS87 property Q
-/

namespace AvgCaseMls.Section3

namespace Hypergraph

/-- Edges meeting `S` in at least two vertices, denoted `N(S)` in CS87. -/
def multiHitEdges (H : Hypergraph n m) (S : Finset (Fin n)) :
    Finset (Fin m) :=
  Finset.univ.filter fun i => 2 ≤ (H.edge i ∩ S).card

noncomputable def normalSets (H : Hypergraph n m) (s : Nat) :
    Finset (Finset (Fin n)) := by
  classical
  let Ω := (Finset.univ : Finset (Fin n)).powersetCard s
  let total := ∑ S ∈ Ω, (H.multiHitEdges S).card
  exact Ω.filter fun S => (H.multiHitEdges S).card * Ω.card ≤ 2 * total

/-- At least half of all `s`-sets are normal. This is the finite, division-free
form of the averaging step immediately before CS87 (5.1). -/
theorem twice_normalSets_card_ge (H : Hypergraph n m) (s : Nat) :
    ((Finset.univ : Finset (Fin n)).powersetCard s).card ≤
      2 * (H.normalSets s).card := by
  classical
  let Ω := (Finset.univ : Finset (Fin n)).powersetCard s
  let f : Finset (Fin n) → Nat := fun S => (H.multiHitEdges S).card
  let B := Ω.filter fun S => 2 * (∑ T ∈ Ω, f T) < f S * Ω.card
  have hB := twice_card_le_of_above_twice_average Ω f
  have hpartition : H.normalSets s ∪ B = Ω := by
    ext S
    simp only [normalSets, Ω, f, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hS, _⟩ | ⟨hS, _⟩) <;> exact hS
    · intro hS
      by_cases hle :
          (H.multiHitEdges S).card * Ω.card ≤
            2 * ∑ T ∈ Ω, f T
      · exact Or.inl ⟨hS, by simpa [Ω, f] using hle⟩
      · refine Or.inr ⟨hS, ?_⟩
        change 2 * (∑ T ∈ Ω, f T) <
          (H.multiHitEdges S).card * Ω.card
        exact Nat.lt_of_not_ge hle
  have hdisj : Disjoint (H.normalSets s) B := by
    rw [Finset.disjoint_left]
    intro S hnormal hbad
    simp only [normalSets, Ω, f, B, Finset.mem_filter] at hnormal hbad
    exact (Nat.not_lt_of_ge hnormal.2) hbad.2
  have hcard :
      (H.normalSets s).card + B.card = Ω.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hpartition]
  change 2 * B.card ≤ Ω.card at hB
  change Ω.card ≤ 2 * (H.normalSets s).card
  omega

/-- The exact indexed-edge pair count used for equation (5.1). -/
theorem multiHit_average_numerator_le
    (H : Hypergraph n m) (hk : H.IsKUniform k) (s : Nat) (hs : 2 ≤ s) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
        (H.multiHitEdges S).card) ≤
      m * k.choose 2 * (n - 2).choose (s - 2) := by
  simpa [multiHitEdges] using H.sum_multiHitEdges_le hk s hs

/-- Equation (5.1) together with normality: a normal `s`-set has at most
`a s / (64k)` multi-hit edges under the paper's choice of `b`. -/
theorem normal_multiHitEdges_bound
    (H : Hypergraph n (c * n)) (hk : H.IsKUniform k)
    (hkpos : 0 < k) (hcpos : 0 < c)
    (a b : ℝ) (ha : 0 ≤ a) (hbnonneg : 0 ≤ b)
    (hb : b ≤ a / (64 * c * k ^ 3))
    (s : Nat) (hs : s = ⌊b * n⌋₊)
    (S : Finset (Fin n)) (hSnormal : S ∈ H.normalSets s) :
    ((H.multiHitEdges S).card : ℝ) ≤ a * s / (64 * k) := by
  classical
  let Ω := (Finset.univ : Finset (Fin n)).powersetCard s
  let total := ∑ T ∈ Ω, (H.multiHitEdges T).card
  have hSΩ : S ∈ Ω := by
    simpa [normalSets, Ω, total] using
      (Finset.mem_filter.mp hSnormal).1
  have hScard : S.card = s := (Finset.mem_powersetCard.mp hSΩ).2
  have hsn : s ≤ n := by
    have := (Finset.mem_powersetCard.mp hSΩ).1
    have := Finset.card_le_card this
    simpa [hScard] using this
  by_cases hs2 : 2 ≤ s
  · have hn2 : 2 ≤ n := hs2.trans hsn
    have hnormal :
        (H.multiHitEdges S).card * Ω.card ≤ 2 * total := by
      simpa [normalSets, Ω, total] using
        (Finset.mem_filter.mp hSnormal).2
    have htotal :
        total ≤ c * n * k.choose 2 * (n - 2).choose (s - 2) := by
      simpa [Ω, total] using H.multiHit_average_numerator_le hk s hs2
    have hchoose :
        n.choose s * s.choose 2 =
          n.choose 2 * (n - 2).choose (s - 2) :=
      Nat.choose_mul hs2
    have hΩcard : Ω.card = n.choose s := by
      simp [Ω]
    have hfirst :
        (H.multiHitEdges S).card * n.choose 2 ≤
          2 * c * n * k.choose 2 * s.choose 2 := by
      have hbase :
          (H.multiHitEdges S).card * n.choose s ≤
            2 * (c * n * k.choose 2 * (n - 2).choose (s - 2)) := by
        rw [← hΩcard]
        exact hnormal.trans (Nat.mul_le_mul_left 2 htotal)
      have hmul := Nat.mul_le_mul_right (n.choose 2) hbase
      have hrearr :
          n.choose s * ((H.multiHitEdges S).card * n.choose 2) ≤
            n.choose s * (2 * c * n * k.choose 2 * s.choose 2) := by
        calc
          n.choose s * ((H.multiHitEdges S).card * n.choose 2) =
              ((H.multiHitEdges S).card * n.choose s) * n.choose 2 := by ring
          _ ≤ (2 * (c * n * k.choose 2 * (n - 2).choose (s - 2))) *
              n.choose 2 := hmul
          _ = 2 * c * n * k.choose 2 *
              (n.choose 2 * (n - 2).choose (s - 2)) := by ring
          _ = 2 * c * n * k.choose 2 *
              (n.choose s * s.choose 2) := by rw [← hchoose]
          _ = n.choose s * (2 * c * n * k.choose 2 * s.choose 2) := by ring
      exact Nat.le_of_mul_le_mul_left hrearr (Nat.choose_pos hsn)
    have hratio := choose_two_ratio_cross hsn
    have hsecond :
        (H.multiHitEdges S).card * n ^ 2 ≤
          2 * c * n * k.choose 2 * s ^ 2 := by
      have hmul := Nat.mul_le_mul_right (n ^ 2) hfirst
      have hbound := Nat.mul_le_mul_left
        (2 * c * n * k.choose 2) hratio
      have hrearr :
          n.choose 2 * ((H.multiHitEdges S).card * n ^ 2) ≤
            n.choose 2 * (2 * c * n * k.choose 2 * s ^ 2) := by
        calc
          n.choose 2 * ((H.multiHitEdges S).card * n ^ 2) =
              ((H.multiHitEdges S).card * n.choose 2) * n ^ 2 := by ring
          _ ≤ (2 * c * n * k.choose 2 * s.choose 2) * n ^ 2 := hmul
          _ ≤ (2 * c * n * k.choose 2) *
              (s ^ 2 * n.choose 2) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hbound
          _ = n.choose 2 * (2 * c * n * k.choose 2 * s ^ 2) := by ring
      exact Nat.le_of_mul_le_mul_left hrearr (Nat.choose_pos hn2)
    have hkchoose := two_mul_choose_two k
    have hkchoose_le : 2 * k.choose 2 ≤ k ^ 2 := by
      rw [hkchoose]
      simpa [pow_two] using Nat.mul_le_mul_left k (Nat.sub_le k 1)
    have hthird :
        (H.multiHitEdges S).card * n ≤ c * k ^ 2 * s ^ 2 := by
      have hnpos : 0 < n := lt_of_lt_of_le (by omega) hn2
      refine Nat.le_of_mul_le_mul_left ?_ hnpos
      calc
        n * ((H.multiHitEdges S).card * n) =
            (H.multiHitEdges S).card * n ^ 2 := by ring
        _ ≤ 2 * c * n * k.choose 2 * s ^ 2 := hsecond
        _ ≤ n * (c * k ^ 2 * s ^ 2) := by
          have := Nat.mul_le_mul_left (c * n * s ^ 2) hkchoose_le
          simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hsbn : (s : ℝ) ≤ b * n := by
      rw [hs]
      exact Nat.floor_le (mul_nonneg hbnonneg (Nat.cast_nonneg _))
    have hthirdR :
        ((H.multiHitEdges S).card : ℝ) * n ≤ c * k ^ 2 * s ^ 2 := by
      exact_mod_cast hthird
    have hnposR : (0 : ℝ) < n := by positivity
    have hkposR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hcposR : (0 : ℝ) < c := by exact_mod_cast hcpos
    have hb' : (c : ℝ) * k ^ 2 * b ≤ a / (64 * k) := by
      calc
        (c : ℝ) * k ^ 2 * b ≤
            c * k ^ 2 * (a / (64 * c * k ^ 3)) := by gcongr
        _ = a / (64 * k) := by field_simp
    have hsposR : (0 : ℝ) < s := by positivity
    have hN :
        ((H.multiHitEdges S).card : ℝ) ≤ c * k ^ 2 * b * s := by
      have hmulN :
          ((H.multiHitEdges S).card : ℝ) * n ≤
            (c * k ^ 2 * b * s) * n := by
        have hsquare : (s : ℝ) ^ 2 ≤ (b * s) * n := by
          calc
            (s : ℝ) ^ 2 = s * s := by ring
            _ ≤ (b * n) * s :=
              mul_le_mul_of_nonneg_right hsbn (Nat.cast_nonneg _)
            _ = (b * s) * n := by ring
        calc
          ((H.multiHitEdges S).card : ℝ) * n ≤ c * k ^ 2 * s ^ 2 :=
            hthirdR
          _ ≤ c * k ^ 2 * ((b * s) * n) := by gcongr
          _ = (c * k ^ 2 * b * s) * n := by ring
      nlinarith
    calc
      ((H.multiHitEdges S).card : ℝ) ≤ c * k ^ 2 * b * s := hN
      _ ≤ (a / (64 * k)) * s := by gcongr
      _ = a * s / (64 * k) := by ring
  · have hNempty : H.multiHitEdges S = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨i, hi⟩
      have hhit : 2 ≤ (H.edge i ∩ S).card :=
        (Finset.mem_filter.mp hi).2
      have hle : (H.edge i ∩ S).card ≤ s := by
        calc
          (H.edge i ∩ S).card ≤ S.card :=
            Finset.card_le_card Finset.inter_subset_right
          _ = s := hScard
      omega
    rw [hNempty]
    norm_num
    exact div_nonneg (mul_nonneg ha (Nat.cast_nonneg _))
      (show (0 : ℝ) ≤ 64 * k by positivity)

/-- CS87 (5.7), directly from local sparsity of the support of `J`. -/
theorem equation_5_7
    (H : Hypergraph n m) (hsparse : H.IsSparse x (1 / 2 + a / 512))
    (J : Finset (Fin m))
    (hsmall : ((H.support J).card : ℝ) ≤ x * n) :
    (2 - a / 128) * J.card ≤ (H.support J).card := by
  have hcontained :
      (J.card : ℝ) ≤ (H.edgesContainedIn (H.support J)).card := by
    exact_mod_cast Finset.card_le_card (H.subset_edgesContainedIn_support J)
  have hs := hsparse (H.support J) hsmall
  have hj :
      (J.card : ℝ) ≤ (1 / 2 + a / 512) * (H.support J).card :=
    hcontained.trans hs
  have hcoef : (1 / 2 + a / 512) * (2 - a / 128) ≤ 1 := by
    nlinarith [sq_nonneg a]
  by_cases hc : 0 ≤ 2 - a / 128
  · calc
      (2 - a / 128) * (J.card : ℝ) ≤
          (2 - a / 128) *
            ((1 / 2 + a / 512) * (H.support J).card) := by gcongr
      _ ≤ 1 * (H.support J).card := by
        have hsupp : 0 ≤ ((H.support J).card : ℝ) := by positivity
        nlinarith
      _ = (H.support J).card := one_mul _
  · have hjnonneg : 0 ≤ ((J.card : ℝ)) := by positivity
    have hsuppnonneg : 0 ≤ ((H.support J).card : ℝ) := by positivity
    nlinarith

/-- CS87 (5.8): vertices of `S` covered by `J` are charged either to one
edge of `J`, or to an edge counted by `N(S)`. -/
theorem equation_5_8
    (H : Hypergraph n m) (hk : H.IsKUniform k)
    (S : Finset (Fin n)) (J : Finset (Fin m)) :
    ((J.biUnion fun i => H.edge i ∩ S).card : ℝ) -
        k * (H.multiHitEdges S).card ≤ J.card := by
  classical
  have hinter : ∀ i : Fin m, (H.edge i ∩ S).card ≤ k := by
    intro i
    calc
      (H.edge i ∩ S).card ≤ (H.edge i).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = k := hk i
  have hpoint : ∀ i ∈ J,
      (H.edge i ∩ S).card ≤
        1 + k * if i ∈ H.multiHitEdges S then 1 else 0 := by
    intro i _
    by_cases hi : i ∈ H.multiHitEdges S
    · simp only [hi, if_true]
      exact (hinter i).trans (by omega)
    · have hlt : (H.edge i ∩ S).card < 2 := by
        simp only [multiHitEdges, Finset.mem_filter, Finset.mem_univ,
          true_and] at hi
        omega
      simp only [hi, if_false, mul_zero, add_zero]
      omega
  have hsum :
      (J.biUnion fun i => H.edge i ∩ S).card ≤
        J.card + k * (H.multiHitEdges S).card := by
    calc
      (J.biUnion fun i => H.edge i ∩ S).card ≤
          ∑ i ∈ J, (H.edge i ∩ S).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ J,
          (1 + k * if i ∈ H.multiHitEdges S then 1 else 0) :=
        Finset.sum_le_sum hpoint
      _ = J.card +
          k * (J.filter fun i => i ∈ H.multiHitEdges S).card := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.card_eq_sum_ones,
          Finset.mul_sum, Finset.sum_filter]
      _ ≤ J.card + k * (H.multiHitEdges S).card := by
        gcongr
        intro i hi
        exact (Finset.mem_filter.mp hi).2
  have hsumR :
      ((J.biUnion fun i => H.edge i ∩ S).card : ℝ) ≤
        J.card + k * (H.multiHitEdges S).card := by
    exact_mod_cast hsum
  linarith

/-- Lemma 2 applied to an indexed hypergraph family. This is the constrained
SDR construction used at (5.2)--(5.6). -/
theorem hasSDRWithAtMost_of_propertyP_and_deficiency
    (H : Hypergraph n m) (hP : H.HasPropertyP a)
    (I : Finset (Fin m)) (hI : (I.card : ℝ) ≤ a * n)
    (S : Finset (Fin n)) (t : Nat)
    (hdef : ∀ J : Finset I,
      J.card - (J.biUnion fun i => H.edge i \ S).card ≤ t) :
    H.HasSDRWithAtMost I S t := by
  have hsdr : H.HasSDR I := H.hasSDR_of_propertyP hP I hI
  have hfamily : FamilyHasSDR (fun i : I => H.edge i) := by
    simpa [FamilyHasSDR, HasSDR] using hsdr
  have hconstrained :
      FamilyHasSDRWithAtMost (fun i : I => H.edge i) S t :=
    (familyHasSDRWithAtMost_iff (fun i : I => H.edge i) S t).2
      ⟨hfamily, hdef⟩
  simpa [FamilyHasSDRWithAtMost, HasSDRWithAtMost] using hconstrained

/-- Every failure of an SDR avoiding `D` contains a minimal Hall obstruction;
its boundary is contained in `D`, hence it is a cluster. -/
theorem exists_cluster_obstruction
    (H : Hypergraph n m) (I : Finset (Fin m)) (D : Finset (Fin n))
    (hno : ¬ H.HasSDRDisjointFrom I D) :
    ∃ J : Finset (Fin m), J ⊆ I ∧ H.IsCluster D J ∧
      ¬ H.HasSDRDisjointFrom J D := by
  classical
  let bad : Finset (Finset I) :=
    Finset.univ.filter fun K =>
      (K.biUnion fun i => H.edge i \ D).card < K.card
  have hbadne : bad.Nonempty := by
    rw [H.hasSDRDisjointFrom_iff_hall] at hno
    push Not at hno
    rcases hno with ⟨K, hK⟩
    exact ⟨K, by simp [bad, hK]⟩
  rcases Finset.exists_min_image bad Finset.card hbadne with
    ⟨K, hKbad, hmin⟩
  let J : Finset (Fin m) := K.image Subtype.val
  have hKineq :
      (K.biUnion fun i => H.edge i \ D).card < K.card := by
    simpa [bad] using hKbad
  have hJsub : J ⊆ I := by
    intro i hi
    simp only [J, Finset.mem_image] at hi
    rcases hi with ⟨j, _, rfl⟩
    exact j.property
  have hKcard : J.card = K.card :=
    Finset.card_image_of_injective K Subtype.val_injective
  have hunion :
      (K.biUnion fun i => H.edge i \ D) =
        J.biUnion fun i => H.edge i \ D := by
    ext v
    simp only [Finset.mem_biUnion, J, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, hv⟩
      exact ⟨i.val, ⟨i, hi, rfl⟩, hv⟩
    · rintro ⟨i, ⟨j, hj, hji⟩, hv⟩
      subst i
      exact ⟨j, hj, hv⟩
  have hJno : ¬ H.HasSDRDisjointFrom J D := by
    rw [H.hasSDRDisjointFrom_iff_hall]
    push Not
    refine ⟨Finset.univ, ?_⟩
    have hJU :
        ((Finset.univ : Finset J).biUnion fun i => H.edge i \ D) =
          J.biUnion fun i => H.edge i \ D := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hv⟩
        exact ⟨i.val, i.property, hv⟩
      · rintro ⟨i, hi, hv⟩
        exact ⟨⟨i, hi⟩, hv⟩
    rw [hJU, ← hunion, Finset.card_univ, Fintype.card_coe, hKcard]
    exact hKineq
  refine ⟨J, hJsub, ?_, hJno⟩
  intro v hv
  by_contra hvD
  have hdeg := (H.mem_boundary J v).mp hv
  simp only [degreeIn, Finset.card_eq_one] at hdeg
  rcases hdeg with ⟨e, he⟩
  have heJ : e ∈ J := by
    have : e ∈ J.filter fun i => v ∈ H.edge i := by simp [he]
    exact (Finset.mem_filter.mp this).1
  rcases Finset.mem_image.mp heJ with ⟨ei, heiK, hei⟩
  have hve : v ∈ H.edge ei.val := by
    have : e ∈ J.filter fun i => v ∈ H.edge i := by simp [he]
    have := (Finset.mem_filter.mp this).2
    simpa [hei] using this
  let K' := K.erase ei
  have hK'card : K'.card = K.card - 1 :=
    Finset.card_erase_of_mem heiK
  have hK'notbad :
      ¬ (K'.biUnion fun i => H.edge i \ D).card < K'.card := by
    intro hbad'
    have hK'mem : K' ∈ bad := by simp [bad, hbad']
    have hle := hmin K' hK'mem
    rw [hK'card] at hle
    omega
  let U := K.biUnion fun i => H.edge i \ D
  let U' := K'.biUnion fun i => H.edge i \ D
  have hU'sub : U' ⊆ U := by
    intro x hx
    simp only [U', U, Finset.mem_biUnion] at hx ⊢
    rcases hx with ⟨i, hi, hxi⟩
    exact ⟨i, (Finset.mem_erase.mp hi).2, hxi⟩
  have hvU : v ∈ U := by
    exact Finset.mem_biUnion.mpr
      ⟨ei, heiK, Finset.mem_sdiff.mpr ⟨hve, hvD⟩⟩
  have hvU' : v ∉ U' := by
    intro hv'
    rcases Finset.mem_biUnion.mp hv' with ⟨i, hiK', hvi⟩
    have hiK := (Finset.mem_erase.mp hiK').2
    have hiJ : i.val ∈ J := Finset.mem_image.mpr ⟨i, hiK, rfl⟩
    have hifilter : i.val ∈ J.filter fun z => v ∈ H.edge z :=
      Finset.mem_filter.mpr ⟨hiJ, (Finset.mem_sdiff.mp hvi).1⟩
    have hie : i.val = e := by
      have := congrArg (fun z => i.val ∈ z) he
      simpa using this.mp hifilter
    have hiiei : i = ei := by
      apply Subtype.ext
      exact hie.trans hei.symm
    exact (Finset.mem_erase.mp hiK').1 hiiei
  have hcardlt : U'.card < U.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hU'sub, fun hEq => hvU' (hEq ▸ hvU)⟩)
  have hU'lower : K'.card ≤ U'.card := Nat.le_of_not_gt hK'notbad
  dsimp [U, U'] at hcardlt hU'lower
  omega

def SmallCluster (H : Hypergraph n m) (a : ℝ)
    (S : Finset (Fin n)) (I : Finset (Fin m)) : Prop :=
  H.IsCluster S I ∧ (I.card : ℝ) ≤ a * n

noncomputable def smallClusters (H : Hypergraph n m) (a : ℝ)
    (S : Finset (Fin n)) : Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.filter fun I => H.SmallCluster a S I

theorem empty_smallCluster (H : Hypergraph n m) (ha : 0 ≤ a)
    (S : Finset (Fin n)) :
    H.SmallCluster a S ∅ := by
  constructor
  · intro v hv
    simp [boundary, degreeIn] at hv
  · simpa using mul_nonneg ha (Nat.cast_nonneg n)

theorem exists_largest_smallCluster
    (H : Hypergraph n m) (ha : 0 ≤ a) (S : Finset (Fin n)) :
    ∃ I, H.SmallCluster a S I ∧
      ∀ J, H.SmallCluster a S J → J.card ≤ I.card := by
  classical
  have hne : (H.smallClusters a S).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [smallClusters, H.empty_smallCluster ha S]
  rcases Finset.exists_max_image (H.smallClusters a S)
      Finset.card hne with ⟨I, hImem, hmax⟩
  refine ⟨I, ?_, ?_⟩
  · simpa [smallClusters] using hImem
  · intro J hJ
    exact hmax J (by simpa [smallClusters] using hJ)

/-- CS87 (5.3)--(5.5): under `4|S| ≤ an`, one largest small cluster
contains every small cluster and has at most `2|S|` edges. -/
theorem exists_universal_smallCluster
    (H : Hypergraph n m) (ha : 0 ≤ a) (hP : H.HasPropertyP a)
    (S : Finset (Fin n))
    (hfour : (4 * S.card : ℝ) ≤ a * n) :
    ∃ I, H.SmallCluster a S I ∧ I.card ≤ 2 * S.card ∧
      ∀ J, H.SmallCluster a S J → J ⊆ I := by
  classical
  rcases H.exists_largest_smallCluster ha S with ⟨I, hI, hmax⟩
  have hIbound : I.card ≤ 2 * S.card :=
    H.cluster_card_le_twice_set hP S I hI.1 hI.2
  refine ⟨I, hI, hIbound, ?_⟩
  intro J hJ
  have hJbound : J.card ≤ 2 * S.card :=
    H.cluster_card_le_twice_set hP S J hJ.1 hJ.2
  have hunionCluster : H.IsCluster S (I ∪ J) :=
    H.cluster_union S I J hI.1 hJ.1
  have hunionCard : ((I ∪ J).card : ℝ) ≤ a * n := by
    have hnat : (I ∪ J).card ≤ 4 * S.card := by
      calc
        (I ∪ J).card ≤ I.card + J.card := Finset.card_union_le I J
        _ ≤ 2 * S.card + 2 * S.card :=
          Nat.add_le_add hIbound hJbound
        _ = 4 * S.card := by omega
    have hnatR : ((I ∪ J).card : ℝ) ≤ 4 * S.card := by
      exact_mod_cast hnat
    exact hnatR.trans hfour
  have hmaxUnion : (I ∪ J).card ≤ I.card :=
    hmax (I ∪ J) ⟨hunionCluster, hunionCard⟩
  have heq : I ∪ J = I := by
    exact (Finset.eq_of_subset_of_card_le
      Finset.subset_union_left hmaxUnion).symm
  exact fun x hx => by
    have : x ∈ I ∪ J := Finset.mem_union_right I hx
    rwa [heq] at this

/-- Turn the constrained SDR of the universal small cluster into the set `D`
required by property Q. Minimal Hall obstructions ensure that the same `D`
works for every small edge family. -/
theorem isQGoodSet_of_universal_constrainedSDR
    (H : Hypergraph n m) (ha : 0 ≤ a) (s : Nat)
    (S : Finset (Fin n)) (hScard : S.card = s)
    (I : Finset (Fin m))
    (huniv : ∀ J, H.SmallCluster a S J → J ⊆ I)
    (hsdr : H.HasSDRWithAtMost I S ⌊(a / 32) * S.card⌋₊) :
    H.IsQGoodSet a s S := by
  classical
  rcases hsdr with ⟨f, hf, hfmem, hfcount⟩
  let A : Finset I := Finset.univ.filter fun i => f i ∈ S
  let R : Finset (Fin n) := A.image f
  let D : Finset (Fin n) := S \ R
  have hDsub : D ⊆ S := Finset.sdiff_subset
  have hSD : S \ D ⊆ R := by
    intro v hv
    have hvS := (Finset.mem_sdiff.mp hv).1
    have hvnotD := (Finset.mem_sdiff.mp hv).2
    by_contra hvnotR
    exact hvnotD (Finset.mem_sdiff.mpr ⟨hvS, hvnotR⟩)
  have hRcard : R.card = A.card :=
    Finset.card_image_of_injective A hf
  have hsmallD : ((S \ D).card : ℝ) ≤ (a / 32) * S.card := by
    have hnat : (S \ D).card ≤ ⌊(a / 32) * S.card⌋₊ := by
      calc
        (S \ D).card ≤ R.card := Finset.card_le_card hSD
        _ = A.card := hRcard
        _ ≤ ⌊(a / 32) * S.card⌋₊ := by simpa [A] using hfcount
    have hfloor :
        (⌊(a / 32) * S.card⌋₊ : ℝ) ≤ (a / 32) * S.card := by
      exact Nat.floor_le (mul_nonneg (div_nonneg ha (by norm_num))
        (Nat.cast_nonneg _))
    have hnatR :
        ((S \ D).card : ℝ) ≤ (⌊(a / 32) * S.card⌋₊ : Nat) := by
      exact_mod_cast hnat
    exact hnatR.trans hfloor
  refine ⟨hScard, D, hDsub, hsmallD, ?_⟩
  intro J hJsmall
  by_contra hno
  rcases H.exists_cluster_obstruction J D hno with
    ⟨K, hKJ, hKclusterD, hKno⟩
  have hKsmall : ((K.card : Nat) : ℝ) ≤ a * n := by
    calc
      (K.card : ℝ) ≤ J.card := by
        exact_mod_cast Finset.card_le_card hKJ
      _ ≤ a * n := hJsmall
  have hKclusterS : H.IsCluster S K := hKclusterD.trans hDsub
  have hKI : K ⊆ I := huniv K ⟨hKclusterS, hKsmall⟩
  let g : K → Fin n := fun i => f ⟨i.val, hKI i.property⟩
  have hg : Function.Injective g := by
    intro i j hij
    have : (⟨i.val, hKI i.property⟩ : I) =
        ⟨j.val, hKI j.property⟩ := hf hij
    apply Subtype.ext
    exact congrArg (fun z : I => z.val) this
  have hgmem : ∀ i : K, g i ∈ H.edge i := by
    intro i
    exact hfmem ⟨i.val, hKI i.property⟩
  have hgD : ∀ i : K, g i ∉ D := by
    intro i hiD
    have hiS : g i ∈ S := hDsub hiD
    have hiA : (⟨i.val, hKI i.property⟩ : I) ∈ A := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiS⟩
    have hiR : g i ∈ R := Finset.mem_image.mpr
      ⟨⟨i.val, hKI i.property⟩, hiA, rfl⟩
    exact (Finset.mem_sdiff.mp hiD).2 hiR
  exact hKno ⟨g, hg, hgmem, hgD⟩

/-- CS87 Lemma 3, property `Q`, with the constants and the two sparsity
assumptions stated in the source. -/
theorem propertyQ_of_sparse
    (H : Hypergraph n (c * n)) (hk : H.IsKUniform k)
    (hkpos : 0 < k) (hcpos : 0 < c)
    (ha : 0 < a) (hx : 0 ≤ x)
    (hsparseP : H.IsSparse (a * k) (4 / (2 * k + 1 : ℝ)))
    (hsparseQ : H.IsSparse x (1 / 2 + a / 512)) :
    H.HasPropertyQ a
      (min (x / (2 * k)) (min (a / (64 * c * k ^ 3)) (a / 8))) := by
  classical
  let b : ℝ :=
    min (x / (2 * k)) (min (a / (64 * c * k ^ 3)) (a / 8))
  let s : Nat := ⌊b * n⌋₊
  let Ω := (Finset.univ : Finset (Fin n)).powersetCard s
  have hkposR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hcposR : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hb0 : 0 ≤ b := by
    dsimp [b]
    positivity
  have hbx : b ≤ x / (2 * k) := min_le_left _ _
  have hba : b ≤ a / (64 * c * k ^ 3) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hb8 : b ≤ a / 8 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hP : H.HasPropertyP a :=
    H.propertyP_of_sparse hk hsparseP
  have hnormalGood : ∀ S ∈ H.normalSets s, H.IsQGoodSet a s S := by
    intro S hSnormal
    have hSΩ : S ∈ Ω := by
      simpa [normalSets, Ω] using (Finset.mem_filter.mp hSnormal).1
    have hScard : S.card = s := (Finset.mem_powersetCard.mp hSΩ).2
    have hsbn : (s : ℝ) ≤ b * n := by
      dsimp [s]
      exact Nat.floor_le (mul_nonneg hb0 (Nat.cast_nonneg _))
    have hfour : (4 * S.card : ℝ) ≤ a * n := by
      rw [hScard]
      calc
        (4 * s : ℝ) ≤ 4 * (b * n) := by gcongr
        _ ≤ 4 * ((a / 8) * n) := by gcongr
        _ ≤ a * n := by
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
          nlinarith
    rcases H.exists_universal_smallCluster (le_of_lt ha) hP S hfour with
      ⟨I, hIsmall, hIcard, huniv⟩
    have hdef : ∀ J : Finset I,
        J.card - (J.biUnion fun i => H.edge i \ S).card ≤
          ⌊(a / 32) * S.card⌋₊ := by
      intro J
      let K : Finset (Fin (c * n)) := J.image Subtype.val
      let P : Finset (Fin n) := K.biUnion fun i => H.edge i ∩ S
      let Q : Finset (Fin n) := K.biUnion fun i => H.edge i \ S
      have hKsub : K ⊆ I := by
        intro i hi
        simp only [K, Finset.mem_image] at hi
        rcases hi with ⟨j, _, rfl⟩
        exact j.property
      have hKcard : K.card = J.card :=
        Finset.card_image_of_injective J Subtype.val_injective
      have hQeq :
          (J.biUnion fun i => H.edge i \ S) = Q := by
        ext v
        simp only [Q, K, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro ⟨i, hi, hv⟩
          exact ⟨i.val, ⟨i, hi, rfl⟩, hv⟩
        · rintro ⟨i, ⟨j, hj, hji⟩, hv⟩
          subst i
          exact ⟨j, hj, hv⟩
      have hKcardle : K.card ≤ 2 * S.card :=
        (Finset.card_le_card hKsub).trans hIcard
      have hsupportNat := H.support_card_le_uniform_incidence hk K
      have hsmallSupport : ((H.support K).card : ℝ) ≤ x * n := by
        have hsuppR :
            ((H.support K).card : ℝ) ≤ (k : ℝ) * K.card := by
          exact_mod_cast hsupportNat
        have hKcardR : (K.card : ℝ) ≤ 2 * S.card := by
          exact_mod_cast hKcardle
        calc
          ((H.support K).card : ℝ) ≤ (k : ℝ) * K.card := hsuppR
          _ ≤ k * (2 * S.card) := by gcongr
          _ = 2 * k * s := by rw [hScard]; ring
          _ ≤ 2 * k * (b * n) := by gcongr
          _ ≤ 2 * k * ((x / (2 * k)) * n) := by gcongr
          _ = x * n := by field_simp
      have hsupportEq : H.support K = P ∪ Q := by
        ext v
        simp only [H.mem_support, P, Q, Finset.mem_union,
          Finset.mem_biUnion, Finset.mem_inter, Finset.mem_sdiff]
        constructor
        · rintro ⟨i, hi, hvi⟩
          by_cases hvS : v ∈ S
          · exact Or.inl ⟨i, hi, hvi, hvS⟩
          · exact Or.inr ⟨i, hi, hvi, hvS⟩
        · rintro (⟨i, hi, hvi, _⟩ | ⟨i, hi, hvi, _⟩)
          · exact ⟨i, hi, hvi⟩
          · exact ⟨i, hi, hvi⟩
      have hPQdisj : Disjoint P Q := by
        rw [Finset.disjoint_left]
        intro v hvP hvQ
        rcases Finset.mem_biUnion.mp hvP with ⟨i, _, hvi⟩
        rcases Finset.mem_biUnion.mp hvQ with ⟨j, _, hvj⟩
        exact (Finset.mem_sdiff.mp hvj).2 (Finset.mem_inter.mp hvi).2
      have h57base := H.equation_5_7 hsparseQ K hsmallSupport
      have hcardPQ :
          ((H.support K).card : ℝ) = (P.card : ℝ) + Q.card := by
        rw [hsupportEq, Finset.card_union_of_disjoint hPQdisj]
        norm_num
      have h57 :
          (2 - a / 128) * (J.card : ℝ) ≤
            (P.card : ℝ) + Q.card := by
        rw [← hKcard]
        exact h57base.trans_eq hcardPQ
      have h58base := H.equation_5_8 hk S K
      have h58 :
          (P.card : ℝ) -
              2 * k * ((H.multiHitEdges S).card / 2 : ℝ) ≤ J.card := by
        dsimp [P]
        rw [← hKcard]
        convert h58base using 1 <;> ring
      have hnormalBound :
          ((H.multiHitEdges S).card : ℝ) ≤ a * s / (64 * k) :=
        H.normal_multiHitEdges_bound hk hkpos hcpos a b
          (le_of_lt ha) hb0 hba s rfl S hSnormal
      have h51 :
          ((H.multiHitEdges S).card / 2 : ℝ) ≤
            a * s / (128 * k) := by
        calc
          ((H.multiHitEdges S).card / 2 : ℝ) ≤
              (a * s / (64 * k)) / 2 := by gcongr
          _ = a * s / (128 * k) := by ring
      have h55 : (J.card : ℝ) ≤ 2 * s := by
        rw [← hKcard]
        exact_mod_cast hKcardle.trans_eq (by rw [hScard])
      have hdefR :
          (J.card : ℝ) - Q.card ≤ a * s / 32 :=
        deficiency_bound_of_cs87_equations h57 h58 h51 h55
          (le_of_lt ha) hkposR
      rw [hQeq]
      by_cases hQJ : Q.card ≤ J.card
      · apply Nat.le_floor
        rw [Nat.cast_sub hQJ]
        rw [hScard]
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdefR
      · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hQJ)]
        exact Nat.zero_le _
    have hconstrained :
        H.HasSDRWithAtMost I S ⌊(a / 32) * S.card⌋₊ :=
      H.hasSDRWithAtMost_of_propertyP_and_deficiency
        hP I hIsmall.2 S _ hdef
    exact H.isQGoodSet_of_universal_constrainedSDR
      (le_of_lt ha) s S hScard I huniv hconstrained
  change 2 * (Ω.filter fun S => H.IsQGoodSet a s S).card ≥ Ω.card
  have hsubset :
      H.normalSets s ⊆ Ω.filter fun S => H.IsQGoodSet a s S := by
    intro S hS
    exact Finset.mem_filter.mpr
      ⟨by simpa [normalSets, Ω] using (Finset.mem_filter.mp hS).1,
        hnormalGood S hS⟩
  calc
    Ω.card ≤ 2 * (H.normalSets s).card := by
      simpa [Ω] using H.twice_normalSets_card_ge s
    _ ≤ 2 * (Ω.filter fun S => H.IsQGoodSet a s S).card := by
      exact Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset)

end Hypergraph

end AvgCaseMls.Section3
