/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Section3.Hypergraph
import AvgCaseMls.Section3.Lemma1Analysis

/-!
# Counting foundations for CS87 local sparsity
-/

namespace AvgCaseMls.Section3

open Filter

noncomputable def containedKSets (S : Finset (Fin n)) (k : Nat) :
    Finset (ClauseVariables n k) := by
  classical
  exact Finset.univ.filter fun T => T.val ⊆ S

private noncomputable def containedKSetsEquiv
    (S : Finset (Fin n)) (k : Nat) :
    {T // T ∈ containedKSets S k} ≃
      {T // T ∈ S.powersetCard k} where
  toFun T := ⟨T.val.val, by
    have h := T.property
    simp only [containedKSets, Finset.mem_filter, Finset.mem_univ,
      true_and] at h
    exact Finset.mem_powersetCard.mpr ⟨h, T.val.property⟩⟩
  invFun T := ⟨⟨T.val, (Finset.mem_powersetCard.mp T.property).2⟩, by
    simp only [containedKSets, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact (Finset.mem_powersetCard.mp T.property).1⟩
  left_inv _T := Subtype.ext rfl
  right_inv T := Subtype.ext rfl

@[simp] theorem containedKSets_card (S : Finset (Fin n)) (k : Nat) :
    (containedKSets S k).card = S.card.choose k := by
  rw [← Fintype.card_coe,
    Fintype.card_congr (containedKSetsEquiv S k), Fintype.card_coe,
    Finset.card_powersetCard]

def EdgesContainedOn
    (G : OrderedKUniformHypergraph n m k)
    (R : Finset (Fin m)) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ R, (G i).val ⊆ S

noncomputable def edgesContainedOnEvent
    (R : Finset (Fin m)) (S : Finset (Fin n)) (k : Nat) :
    Finset (OrderedKUniformHypergraph n m k) := by
  classical
  exact Finset.univ.filter fun G => EdgesContainedOn G R S

@[simp] theorem mem_edgesContainedOnEvent
    (G : OrderedKUniformHypergraph n m k)
    (R : Finset (Fin m)) (S : Finset (Fin n)) :
    G ∈ edgesContainedOnEvent R S k ↔ EdgesContainedOn G R S := by
  classical
  simp [edgesContainedOnEvent]

/-- The choices available at one coordinate under a containment constraint. -/
abbrev ConstrainedEdgeChoice
    (R : Finset (Fin m)) (S : Finset (Fin n)) (k : Nat) (i : Fin m) :=
  {T : ClauseVariables n k // i ∈ R → T.val ⊆ S}

private noncomputable def edgesContainedOnEquiv
    (R : Finset (Fin m)) (S : Finset (Fin n)) (k : Nat) :
    {G // G ∈ edgesContainedOnEvent R S k} ≃
      ((i : Fin m) → ConstrainedEdgeChoice R S k i) where
  toFun G i := ⟨G.val i, fun hi =>
    (mem_edgesContainedOnEvent G.val R S).mp G.property i hi⟩
  invFun f := ⟨fun i => (f i).val, by
    rw [mem_edgesContainedOnEvent]
    intro i hi
    exact (f i).property hi⟩
  left_inv G := Subtype.ext (funext fun _ => rfl)
  right_inv f := funext fun _ => Subtype.ext rfl

private noncomputable def constrainedEdgeChoiceEquivContained
    (R : Finset (Fin m)) (S : Finset (Fin n)) (k : Nat)
    (i : Fin m) (hi : i ∈ R) :
    ConstrainedEdgeChoice R S k i ≃
      {T // T ∈ containedKSets S k} where
  toFun T := ⟨T.val, by
    simp only [containedKSets, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact T.property hi⟩
  invFun T := ⟨T.val, fun _ => by
    simpa [containedKSets] using T.property⟩
  left_inv _T := Subtype.ext rfl
  right_inv T := Subtype.ext rfl

private noncomputable def constrainedEdgeChoiceEquivAll
    (R : Finset (Fin m)) (S : Finset (Fin n)) (k : Nat)
    (i : Fin m) (hi : i ∉ R) :
    ConstrainedEdgeChoice R S k i ≃ ClauseVariables n k where
  toFun T := T.val
  invFun _T := ⟨_T, fun h => (hi h).elim⟩
  left_inv _T := Subtype.ext rfl
  right_inv _ := rfl

theorem constrainedEdgeChoice_card
    (R : Finset (Fin m)) (S : Finset (Fin n)) (k : Nat) (i : Fin m) :
    Fintype.card (ConstrainedEdgeChoice R S k i) =
      if i ∈ R then S.card.choose k else n.choose k := by
  classical
  split_ifs with hi
  · rw [Fintype.card_congr
      (constrainedEdgeChoiceEquivContained R S k i hi),
      Fintype.card_coe, containedKSets_card]
  · rw [Fintype.card_congr
      (constrainedEdgeChoiceEquivAll R S k i hi),
      clauseVariables_card]

/-- Exact product count for prescribed edge coordinates. This is the
independence/counting identity needed in CS87 Lemma 1. -/
theorem edgesContainedOnEvent_card
    (R : Finset (Fin m)) (S : Finset (Fin n)) (k : Nat) :
    (edgesContainedOnEvent R S k).card =
      (S.card.choose k) ^ R.card *
        (n.choose k) ^ (m - R.card) := by
  classical
  rw [← Fintype.card_coe,
    Fintype.card_congr (edgesContainedOnEquiv R S k),
    Fintype.card_pi]
  simp_rw [constrainedEdgeChoice_card]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hcomp :
      ({i : Fin m | i ∉ R} : Finset (Fin m)).card = m - R.card := by
    have heq : ({i : Fin m | i ∉ R} : Finset (Fin m)) = Rᶜ := by
      ext i
      simp
    rw [heq, Finset.card_compl]
    simp
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hcomp]

set_option linter.style.haveILetI false in
/-- Exact probability that every coordinate in `R` lands inside `S`. -/
theorem edgesContainedOnEvent_probability
    (hk : k ≤ n) (R : Finset (Fin m)) (S : Finset (Fin n)) :
    (randomOrderedKUniformHypergraphOfLE n m k hk).eventProb
        (edgesContainedOnEvent R S k :
          Set (OrderedKUniformHypergraph n m k)) =
      (((S.card.choose k : Nat) : ℝ) / n.choose k) ^ R.card := by
  let C := positiveOrdinaryClause hk
  letI : Nonempty (ClauseVariables n k) := ⟨C.1⟩
  change (FinitePMF.uniform (OrderedKUniformHypergraph n m k)).eventProb
      (edgesContainedOnEvent R S k :
        Set (OrderedKUniformHypergraph n m k)) = _
  rw [FinitePMF.uniform_eventProb, edgesContainedOnEvent_card,
    orderedKUniformHypergraph_cardinality]
  have hN : ((n.choose k : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hRm : R.card ≤ m := by
    simpa using Finset.card_le_univ R
  have hm : m = R.card + (m - R.card) := by omega
  have hpow :
      (n.choose k) ^ m =
        (n.choose k) ^ R.card * (n.choose k) ^ (m - R.card) := by
    conv_lhs => rw [hm, pow_add]
  rw [hpow]
  push_cast
  rw [div_pow]
  rw [mul_div_mul_right _ _ (pow_ne_zero _ hN)]

noncomputable def atLeastContainedEvent
    (S : Finset (Fin n)) (r m k : Nat) :
    Finset (OrderedKUniformHypergraph n m k) := by
  classical
  exact Finset.univ.filter fun G =>
    r ≤ (G.toHypergraph.edgesContainedIn S).card

/-- Every outcome with at least `r` contained edges has a prescribed
`r`-coordinate witness. This is the union-bound reduction behind the
binomial tail estimate in CS87 Lemma 1. -/
theorem atLeastContainedEvent_subset_witness_union
    (S : Finset (Fin n)) (r m k : Nat) :
    atLeastContainedEvent S r m k ⊆
      (Finset.univ.powersetCard r).biUnion fun R =>
        edgesContainedOnEvent R S k := by
  classical
  intro G hG
  simp only [atLeastContainedEvent, Finset.mem_filter, Finset.mem_univ,
    true_and] at hG
  let A := G.toHypergraph.edgesContainedIn S
  obtain ⟨R, hRA, hRcard⟩ :=
    Finset.exists_subset_card_eq hG
  simp only [Finset.mem_biUnion, Finset.mem_powersetCard]
  refine ⟨R, ⟨Finset.subset_univ R, hRcard⟩, ?_⟩
  rw [mem_edgesContainedOnEvent]
  intro i hi
  have hiA := hRA hi
  rw [Hypergraph.mem_edgesContainedIn] at hiA
  exact hiA

/-- Exact finite union bound for a binomial upper tail in the ordered
hypergraph model. -/
theorem atLeastContainedEvent_card_le
    (S : Finset (Fin n)) (r m k : Nat) :
    (atLeastContainedEvent S r m k).card ≤
      m.choose r *
        ((S.card.choose k) ^ r * (n.choose k) ^ (m - r)) := by
  classical
  calc
    (atLeastContainedEvent S r m k).card ≤
        ((Finset.univ.powersetCard r).biUnion fun R =>
          edgesContainedOnEvent R S k).card :=
      Finset.card_le_card
        (atLeastContainedEvent_subset_witness_union S r m k)
    _ ≤ ∑ R ∈ Finset.univ.powersetCard r,
        (edgesContainedOnEvent R S k).card := Finset.card_biUnion_le
    _ = ∑ _R ∈ Finset.univ.powersetCard r,
        ((S.card.choose k) ^ r * (n.choose k) ^ (m - r)) := by
      apply Finset.sum_congr rfl
      intro R hR
      rw [edgesContainedOnEvent_card]
      have := (Finset.mem_powersetCard.mp hR).2
      rw [this]
    _ = m.choose r *
        ((S.card.choose k) ^ r * (n.choose k) ^ (m - r)) := by
      rw [Finset.sum_const, Finset.card_powersetCard]
      simp

set_option linter.style.haveILetI false in
/-- Probability form of the finite binomial-tail union bound. -/
theorem atLeastContainedEvent_probability_le
    (hk : k ≤ n) (hr : r ≤ m) (S : Finset (Fin n)) :
    (randomOrderedKUniformHypergraphOfLE n m k hk).eventProb
        (atLeastContainedEvent S r m k :
          Set (OrderedKUniformHypergraph n m k)) ≤
      (m.choose r : ℝ) *
        (((S.card.choose k : Nat) : ℝ) / n.choose k) ^ r := by
  let C := positiveOrdinaryClause hk
  letI : Nonempty (ClauseVariables n k) := ⟨C.1⟩
  change (FinitePMF.uniform (OrderedKUniformHypergraph n m k)).eventProb
      (atLeastContainedEvent S r m k :
        Set (OrderedKUniformHypergraph n m k)) ≤ _
  rw [FinitePMF.uniform_eventProb, orderedKUniformHypergraph_cardinality]
  push_cast
  have hN : ((n.choose k : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  have hcard := atLeastContainedEvent_card_le S r m k
  have hden : 0 ≤ ((n.choose k : Nat) : ℝ) ^ m := by positivity
  calc
    ((atLeastContainedEvent S r m k).card : ℝ) /
          ((n.choose k : Nat) : ℝ) ^ m ≤
        ((m.choose r : Nat) : ℝ) *
            (((S.card.choose k : Nat) : ℝ) ^ r *
              ((n.choose k : Nat) : ℝ) ^ (m - r)) /
          ((n.choose k : Nat) : ℝ) ^ m := by
      apply div_le_div_of_nonneg_right _ hden
      exact_mod_cast hcard
    _ = (m.choose r : ℝ) *
        (((S.card.choose k : Nat) : ℝ) / n.choose k) ^ r := by
      have hm : m = r + (m - r) := by omega
      have hpow :
          ((n.choose k : Nat) : ℝ) ^ m =
            ((n.choose k : Nat) : ℝ) ^ r *
              ((n.choose k : Nat) : ℝ) ^ (m - r) := by
        conv_lhs => rw [hm, pow_add]
      rw [hpow, div_pow]
      rw [mul_div_assoc]
      congr 1
      rw [mul_div_mul_right _ _ (pow_ne_zero _ hN)]

/-- The least integer strictly larger than `y*s`. -/
noncomputable def sparseViolationThreshold (y : ℝ) (s : Nat) : Nat :=
  ⌊y * s⌋₊ + 1

noncomputable def smallVertexSets (n : Nat) (x : ℝ) :
    Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun S => (S.card : ℝ) ≤ x * n

noncomputable def nonSparseEvent (n m k : Nat) (x y : ℝ) :
    Finset (OrderedKUniformHypergraph n m k) := by
  classical
  exact Finset.univ.filter fun G => ¬G.toHypergraph.IsSparse x y

/-- Failure of `(x,y)`-sparsity has a vertex set and a threshold-sized
coordinate witness. -/
theorem nonSparseEvent_subset_vertex_union
    (hy : 0 ≤ y) (n m k : Nat) (x : ℝ) :
    nonSparseEvent n m k x y ⊆
      (smallVertexSets n x).biUnion fun S =>
        atLeastContainedEvent S (sparseViolationThreshold y S.card) m k := by
  classical
  intro G hG
  simp only [nonSparseEvent, Finset.mem_filter, Finset.mem_univ,
    true_and] at hG
  simp only [Hypergraph.IsSparse, not_forall, not_le] at hG
  rcases hG with ⟨S, hsmall, hmany⟩
  simp only [Finset.mem_biUnion]
  refine ⟨S, ?_, ?_⟩
  · simp [smallVertexSets, hsmall]
  · simp only [atLeastContainedEvent, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hyS : 0 ≤ y * (S.card : ℝ) :=
      mul_nonneg hy (Nat.cast_nonneg _)
    have hfloor :
        ⌊y * (S.card : ℝ)⌋₊ <
          (G.toHypergraph.edgesContainedIn S).card := by
      rw [Nat.floor_lt hyS]
      exact hmany
    exact Nat.add_one_le_iff.mpr hfloor

/-- The complete finite union sum from which CS87 Lemma 1's two-range
asymptotic estimate is obtained. -/
theorem nonSparseEvent_card_le_union_sum
    (hy : 0 ≤ y) (n m k : Nat) (x : ℝ) :
    (nonSparseEvent n m k x y).card ≤
      ∑ S ∈ smallVertexSets n x,
        m.choose (sparseViolationThreshold y S.card) *
          ((S.card.choose k) ^ (sparseViolationThreshold y S.card) *
            (n.choose k) ^
              (m - sparseViolationThreshold y S.card)) := by
  classical
  calc
    (nonSparseEvent n m k x y).card ≤
        ((smallVertexSets n x).biUnion fun S =>
          atLeastContainedEvent S
            (sparseViolationThreshold y S.card) m k).card :=
      Finset.card_le_card
        (nonSparseEvent_subset_vertex_union hy n m k x)
    _ ≤ ∑ S ∈ smallVertexSets n x,
        (atLeastContainedEvent S
          (sparseViolationThreshold y S.card) m k).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ S ∈ smallVertexSets n x,
        m.choose (sparseViolationThreshold y S.card) *
          ((S.card.choose k) ^ (sparseViolationThreshold y S.card) *
            (n.choose k) ^
              (m - sparseViolationThreshold y S.card)) := by
      exact Finset.sum_le_sum fun S _ =>
        atLeastContainedEvent_card_le S
          (sparseViolationThreshold y S.card) m k

/-- The linear-density random hypergraph family, indexed from `n = k`. -/
noncomputable def denseRandomHypergraph (c k r : Nat) :
    FinitePMF
      (OrderedKUniformHypergraph (r + k) (c * (r + k)) k) :=
  randomOrderedKUniformHypergraphOfLE
    (r + k) (c * (r + k)) k (Nat.le_add_left k r)

/-- Failure of sparsity for the linear-density family. -/
noncomputable def denseNonSparseEvent (c k : Nat) (x y : ℝ) (r : Nat) :
    Set (OrderedKUniformHypergraph (r + k) (c * (r + k)) k) :=
  nonSparseEvent (r + k) (c * (r + k)) k x y

/-- The desired `(x,y)`-sparsity event. -/
noncomputable def denseSparseEvent (c k : Nat) (x y : ℝ) (r : Nat) :
    Set (OrderedKUniformHypergraph (r + k) (c * (r + k)) k) :=
  (denseNonSparseEvent c k x y r)ᶜ

set_option linter.style.haveILetI false in
/--
Probability form of the complete finite union bound, before CS87's
small/large-`s` estimates.
-/
theorem dense_nonSparse_probability_le_complete_union_sum
    (hy : 0 ≤ y) (c k r : Nat) (x : ℝ) :
    (denseRandomHypergraph c k r).eventProb
        (denseNonSparseEvent c k x y r) ≤
      ((∑ S ∈ smallVertexSets (r + k) x,
          (c * (r + k)).choose
              (sparseViolationThreshold y S.card) *
            ((S.card.choose k) ^
                (sparseViolationThreshold y S.card) *
              ((r + k).choose k) ^
                (c * (r + k) -
                  sparseViolationThreshold y S.card)) : Nat) : ℝ) /
        (((r + k).choose k : Nat) : ℝ) ^ (c * (r + k)) := by
  let C := positiveOrdinaryClause (Nat.le_add_left k r)
  letI : Nonempty (ClauseVariables (r + k) k) := ⟨C.1⟩
  change
    (FinitePMF.uniform
      (OrderedKUniformHypergraph (r + k) (c * (r + k)) k)).eventProb
        (nonSparseEvent (r + k) (c * (r + k)) k x y :
          Set (OrderedKUniformHypergraph (r + k) (c * (r + k)) k)) ≤ _
  rw [FinitePMF.uniform_eventProb,
    orderedKUniformHypergraph_cardinality]
  push_cast
  apply div_le_div_of_nonneg_right
  · exact_mod_cast
      nonSparseEvent_card_le_union_sum hy (r + k) (c * (r + k)) k x
  · positivity

theorem sum_smallVertexSets_card_eq (n : Nat) (x : ℝ) (q : Nat → ℝ) :
    ∑ S ∈ smallVertexSets n x, q S.card =
      ∑ s ∈ cs87SummationIndices n 0 x, (n.choose s : ℝ) * q s := by
  classical
  calc
    ∑ S ∈ smallVertexSets n x, q S.card =
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          if (S.card : ℝ) ≤ x * n then q S.card else 0 := by
            rw [Finset.powerset_univ]
            simp only [smallVertexSets, Finset.sum_filter]
    _ = ∑ s ∈ Finset.range (n + 1),
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
          if (S.card : ℝ) ≤ x * n then q S.card else 0 := by
            rw [Finset.sum_powerset]
            simp
    _ = ∑ s ∈ Finset.range (n + 1),
        (n.choose s : ℝ) * (if (s : ℝ) ≤ x * n then q s else 0) := by
            apply Finset.sum_congr rfl
            intro s _
            calc
              (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
                  if (S.card : ℝ) ≤ x * n then q S.card else 0) =
                  ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
                    (if (s : ℝ) ≤ x * n then q s else 0) := by
                      apply Finset.sum_congr rfl
                      intro S hS
                      rw [(Finset.mem_powersetCard.mp hS).2]
              _ = (n.choose s : ℝ) *
                  (if (s : ℝ) ≤ x * n then q s else 0) := by
                    rw [Finset.sum_const, Finset.card_powersetCard]
                    simp
    _ = ∑ s ∈ cs87SummationIndices n 0 x,
        (n.choose s : ℝ) * q s := by
            rw [cs87SummationIndices, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro s _
            simp

theorem normalized_union_term_eq
    (hk : k ≤ n) (m s R : Nat) :
    ((m.choose R * (s.choose k ^ R * n.choose k ^ (m - R)) : Nat) : ℝ) /
        (((n.choose k : Nat) : ℝ) ^ m) =
      (m.choose R : ℝ) *
        (((s.choose k : Nat) : ℝ) / n.choose k) ^ R := by
  have hN : ((n.choose k : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  by_cases hR : R ≤ m
  · have hm : m = R + (m - R) := by omega
    have hpow : (((n.choose k : Nat) : ℝ) ^ m) =
        (((n.choose k : Nat) : ℝ) ^ R) *
          (((n.choose k : Nat) : ℝ) ^ (m - R)) := by
      conv_lhs => rw [hm, pow_add]
    push_cast
    rw [hpow, div_pow]
    field_simp
  · have hmR : m < R := lt_of_not_ge hR
    rw [Nat.choose_eq_zero_of_lt hmR]
    simp

theorem dense_nonSparse_probability_le_envelopeSum
    {c k : Nat} {y : ℝ} (hc : 0 < c) (hk : 1 < k)
    (hy : 1 < ((k - 1 : Nat) : ℝ) * y) (r : Nat) :
    (denseRandomHypergraph c k r).eventProb
        (denseNonSparseEvent c k (cs87LocalSparsityX c k y) y r) ≤
      cs87EnvelopeSum c k y (cs87LocalSparsityX c k y) (r + k) := by
  let n := r + k
  let m := c * n
  let q : Nat → ℝ := fun s =>
    (m.choose (sparseViolationThreshold y s) : ℝ) *
      (((s.choose k : Nat) : ℝ) / n.choose k) ^
        sparseViolationThreshold y s
  have hn : k ≤ n := Nat.le_add_left k r
  have hy0 : 0 ≤ y := by
    have hkm1 : (0 : ℝ) < (k - 1 : Nat) := by
      exact_mod_cast Nat.sub_pos_of_lt hk
    nlinarith
  calc
    (denseRandomHypergraph c k r).eventProb
        (denseNonSparseEvent c k (cs87LocalSparsityX c k y) y r) ≤
      ((∑ S ∈ smallVertexSets n (cs87LocalSparsityX c k y),
          m.choose (sparseViolationThreshold y S.card) *
            (S.card.choose k ^ sparseViolationThreshold y S.card *
              n.choose k ^ (m - sparseViolationThreshold y S.card)) : Nat) : ℝ) /
        (((n.choose k : Nat) : ℝ) ^ m) := by
          simpa [n, m] using
            dense_nonSparse_probability_le_complete_union_sum hy0 c k r
              (cs87LocalSparsityX c k y)
    _ = ∑ S ∈ smallVertexSets n (cs87LocalSparsityX c k y), q S.card := by
          push_cast
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro S _
          simpa [q, Nat.cast_mul] using normalized_union_term_eq hn m S.card
            (sparseViolationThreshold y S.card)
    _ = ∑ s ∈ cs87SummationIndices n 0 (cs87LocalSparsityX c k y),
          (n.choose s : ℝ) * q s :=
      sum_smallVertexSets_card_eq n (cs87LocalSparsityX c k y) q
    _ ≤ cs87EnvelopeSum c k y (cs87LocalSparsityX c k y) n := by
      rw [cs87EnvelopeSum, cs87SummationIndices, cs87SummationIndices]
      rw [Finset.sum_filter, Finset.sum_filter]
      simp only [Nat.zero_le, true_and]
      apply Finset.sum_le_sum
      intro s hs
      split_ifs with hsx hright
      · have hks : k ≤ s := hright.1
        have hsn : s ≤ n := by
          have := Finset.mem_range.mp hs
          omega
        have hthreshold :
            y * (s : ℝ) < (sparseViolationThreshold y s : Nat) := by
          simpa [sparseViolationThreshold] using
            Nat.lt_floor_add_one (y * (s : ℝ))
        simpa [q, m, mul_assoc] using
          cs87_aggregate_coefficient_le_envelope hc hk hy hks hsn
            hsx hthreshold
      · have hsk : s < k := by
          simpa [hsx] using hright
        have hthpos : 0 < sparseViolationThreshold y s := by
          simp [sparseViolationThreshold]
        simp [q, Nat.choose_eq_zero_of_lt hsk, zero_pow hthpos.ne']
      · unfold cs87Envelope
        positivity
      all_goals norm_num

theorem dense_nonSparse_probability_tendsto_zero
    {c k : Nat} {y : ℝ} (hc : 0 < c) (hk : 1 < k)
    (hy : 1 < ((k - 1 : Nat) : ℝ) * y) :
    Tendsto (fun r =>
      (denseRandomHypergraph c k r).eventProb
        (denseNonSparseEvent c k (cs87LocalSparsityX c k y) y r))
      atTop (nhds 0) := by
  have hf := cs87_smallRatio_tendsto_zero (c := c) (k := k) (y := y)
    hc hk hy
  have hfshift : Tendsto (fun r => cs87SmallRatio c k y (r + k))
      atTop (nhds 0) := (Filter.tendsto_add_atTop_iff_nat k).2 hf
  have hflt : ∀ᶠ r : Nat in atTop, cs87SmallRatio c k y (r + k) < 1 :=
    (tendsto_order.1 hfshift).2 1 zero_lt_one
  have hmajor := cs87_splitMajorant_tendsto_zero
    (c := c) (k := k) (y := y) hc hk hy
  have hmajorShift : Tendsto (fun r => cs87SplitMajorant c k y (r + k))
      atTop (nhds 0) := (Filter.tendsto_add_atTop_iff_nat k).2 hmajor
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun r =>
      lt_of_lt_of_le ha
        ((denseRandomHypergraph c k r).eventProb_nonneg _)
  · intro a ha
    have hma := (tendsto_order.1 hmajorShift).2 a ha
    filter_upwards [hflt, hma] with r hfr hmar
    exact lt_of_le_of_lt
      ((dense_nonSparse_probability_le_envelopeSum hc hk hy r).trans
        (cs87_envelopeSum_le_splitMajorant hc hk hy
          (Nat.add_pos_right r (lt_trans Nat.zero_lt_one hk)) hfr))
      hmar

theorem dense_sparse_probability_tendsto_one
    {c k : Nat} {y : ℝ} (hc : 0 < c) (hk : 1 < k)
    (hy : 1 < ((k - 1 : Nat) : ℝ) * y) :
    Tendsto (fun r =>
      (denseRandomHypergraph c k r).eventProb
        (denseSparseEvent c k (cs87LocalSparsityX c k y) y r))
      atTop (nhds 1) := by
  have hzero := dense_nonSparse_probability_tendsto_zero hc hk hy
  have hone : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hsub := hone.sub hzero
  simpa [denseSparseEvent, FinitePMF.eventProb_compl] using hsub

/-- CS87 Lemma 1 with the paper's exact choices of `ε`, `x`, `f`, and
the split at `g(n) = √n`. -/
theorem cs87_local_sparsity_withHighProbability
    {c k : Nat} {y : ℝ} (hc : 0 < c) (hk : 0 < k)
    (hy : 1 < ((k - 1 : Nat) : ℝ) * y) :
    WithHighProbability (denseRandomHypergraph c k)
      (denseSparseEvent c k (cs87LocalSparsityX c k y) y) := by
  have hk2 : 1 < k := by
    by_contra h
    have hkle : k ≤ 1 := Nat.le_of_not_gt h
    have hk1 : k = 1 := by omega
    norm_num [hk1] at hy
  exact dense_sparse_probability_tendsto_one hc hk2 hy

theorem cs87_local_sparsity_exists
    {c k : Nat} {y : ℝ} (hc : 0 < c) (hk : 0 < k)
    (hy : 1 < ((k - 1 : Nat) : ℝ) * y) :
    ∃ x : ℝ, 0 < x ∧
      WithHighProbability (denseRandomHypergraph c k)
        (denseSparseEvent c k x y) := by
  have hk2 : 1 < k := by
    by_contra h
    have hk1 : k = 1 := by omega
    norm_num [hk1] at hy
  exact ⟨cs87LocalSparsityX c k y,
    cs87_localSparsityX_pos hc hk2 hy,
    cs87_local_sparsity_withHighProbability hc hk hy⟩

end AvgCaseMls.Section3
