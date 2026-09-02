/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Section3.RandomCNF
import Mathlib.Combinatorics.Hall.Finite

/-!
# Ordered finite hypergraphs and clause projection
-/

namespace AvgCaseMls.Section3

/-- A system of distinct representatives for an arbitrary finite family. -/
def FamilyHasSDR {ι α : Type*} [Fintype ι] [Fintype α]
    (E : ι → Finset α) : Prop :=
  ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ E i

/-- A system of distinct representatives using at most `t` points of `S`. -/
def FamilyHasSDRWithAtMost {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α]
    (E : ι → Finset α) (S : Finset α) (t : Nat) : Prop := by
  exact ∃ f : ι → α, Function.Injective f ∧ (∀ i, f i ∈ E i) ∧
    (Finset.univ.filter fun i => f i ∈ S).card ≤ t

/-- The necessary half of CS87 Lemma 2, with the exact deficiency bound. -/
theorem familyHasSDRWithAtMost_onlyIf {ι α : Type*}
    [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]
    (E : ι → Finset α) (S : Finset α) (t : Nat)
    (h : FamilyHasSDRWithAtMost E S t) :
    FamilyHasSDR E ∧
      ∀ J : Finset ι,
        J.card - (J.biUnion fun i => E i \ S).card ≤ t := by
  classical
  rcases h with ⟨f, hf, hmem, hcount⟩
  refine ⟨⟨f, hf, hmem⟩, ?_⟩
  intro J
  let A := J.filter fun i => f i ∈ S
  let B := J.filter fun i => f i ∉ S
  have hpartition : A ∪ B = J := by
    ext i
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    by_cases hi : i ∈ J <;> by_cases hs : f i ∈ S <;> simp_all
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    exact (Finset.mem_filter.mp hiB).2 (Finset.mem_filter.mp hiA).2
  have hcardJ : J.card = A.card + B.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hpartition]
  have hAle : A.card ≤ t := by
    have hsub : A ⊆ Finset.univ.filter fun i => f i ∈ S := by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
    exact le_trans (Finset.card_le_card hsub) hcount
  have hB : B.image f ⊆ J.biUnion fun i => E i \ S := by
    intro x hx
    simp only [Finset.mem_image] at hx
    rcases hx with ⟨i, hiB, rfl⟩
    have hiJ : i ∈ J := (Finset.mem_filter.mp hiB).1
    have hnot : f i ∉ S := (Finset.mem_filter.mp hiB).2
    exact Finset.mem_biUnion.mpr
      ⟨i, hiJ, Finset.mem_sdiff.mpr ⟨hmem i, hnot⟩⟩
  have hBle : B.card ≤ (J.biUnion fun i => E i \ S).card := by
    rw [← Finset.card_image_of_injective B hf]
    exact Finset.card_le_card hB
  omega

/--
A hypergraph with named vertices and ordered, not-necessarily-distinct edges.
The edge indices preserve multiplicity.
-/
structure Hypergraph (n m : Nat) where
  edge : Fin m → Finset (Fin n)
  deriving DecidableEq, Fintype

namespace Hypergraph

def IsKUniform (H : Hypergraph n m) (k : Nat) : Prop :=
  ∀ i, (H.edge i).card = k

def edgesContainedIn (H : Hypergraph n m) (S : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun i => H.edge i ⊆ S

def IsSparse (H : Hypergraph n m) (x y : ℝ) : Prop :=
  ∀ S : Finset (Fin n), (S.card : ℝ) ≤ x * n →
    ((H.edgesContainedIn S).card : ℝ) ≤ y * S.card

def degreeIn (H : Hypergraph n m) (I : Finset (Fin m)) (v : Fin n) : Nat :=
  (I.filter fun i => v ∈ H.edge i).card

def boundary (H : Hypergraph n m) (I : Finset (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter fun v => H.degreeIn I v = 1

/-- The vertices covered by a family of edge indices. -/
def support (H : Hypergraph n m) (I : Finset (Fin m)) : Finset (Fin n) :=
  I.biUnion H.edge

/-- A system of distinct representatives for the indexed edge family `I`. -/
def HasSDR (H : Hypergraph n m) (I : Finset (Fin m)) : Prop :=
  ∃ f : I → Fin n, Function.Injective f ∧ ∀ i : I, f i ∈ H.edge i

/-- An SDR none of whose representatives lies in `D`. -/
def HasSDRDisjointFrom (H : Hypergraph n m) (I : Finset (Fin m))
    (D : Finset (Fin n)) : Prop :=
  ∃ f : I → Fin n, Function.Injective f ∧
    (∀ i : I, f i ∈ H.edge i) ∧ ∀ i : I, f i ∉ D

/-- An SDR using at most `t` representatives in `S`. -/
def HasSDRWithAtMost (H : Hypergraph n m) (I : Finset (Fin m))
    (S : Finset (Fin n)) (t : Nat) : Prop :=
  ∃ f : I → Fin n, Function.Injective f ∧
    (∀ i : I, f i ∈ H.edge i) ∧
      (Finset.univ.filter fun i : I => f i ∈ S).card ≤ t

/-- CS87's property `P(a)`. Edge families are families of indices, hence
repeated equal edges retain their multiplicity. -/
def HasPropertyP (H : Hypergraph n m) (a : ℝ) : Prop :=
  ∀ I : Finset (Fin m), (I.card : ℝ) ≤ a * n →
    (I.card : ℝ) / 2 ≤ (H.boundary I).card

/-- The sets counted as good in CS87's property `Q(a,b)`. -/
def IsQGoodSet (H : Hypergraph n m) (a : ℝ) (s : Nat)
    (S : Finset (Fin n)) : Prop :=
  S.card = s ∧ ∃ D : Finset (Fin n), D ⊆ S ∧
    ((S \ D).card : ℝ) ≤ (a / 32) * S.card ∧
    ∀ I : Finset (Fin m), (I.card : ℝ) ≤ a * n →
      H.HasSDRDisjointFrom I D

/-- CS87's property `Q(a,b)`: at least half of all `⌊bn⌋`-sets are good. -/
noncomputable def HasPropertyQ (H : Hypergraph n m) (a b : ℝ) : Prop := by
  classical
  let s := ⌊b * n⌋₊
  exact 2 * (((Finset.univ : Finset (Fin n)).powersetCard s).filter fun S =>
    H.IsQGoodSet a s S).card ≥
      ((Finset.univ : Finset (Fin n)).powersetCard s).card

/-- A cluster is a family of edges whose boundary is contained in `S`. -/
def IsCluster (H : Hypergraph n m) (S : Finset (Fin n))
    (I : Finset (Fin m)) : Prop :=
  H.boundary I ⊆ S

@[simp] theorem mem_edgesContainedIn (H : Hypergraph n m) (S : Finset (Fin n))
    (i : Fin m) : i ∈ H.edgesContainedIn S ↔ H.edge i ⊆ S := by
  simp [edgesContainedIn]

@[simp] theorem mem_boundary (H : Hypergraph n m) (I : Finset (Fin m))
    (v : Fin n) : v ∈ H.boundary I ↔ H.degreeIn I v = 1 := by
  simp [boundary]

@[simp] theorem mem_support (H : Hypergraph n m) (I : Finset (Fin m))
    (v : Fin n) : v ∈ H.support I ↔ ∃ i ∈ I, v ∈ H.edge i := by
  simp [support]

theorem sum_degreeIn (H : Hypergraph n m) (I : Finset (Fin m)) :
    ∑ v : Fin n, H.degreeIn I v = ∑ i ∈ I, (H.edge i).card := by
  classical
  calc
    ∑ v : Fin n, H.degreeIn I v =
        ∑ v : Fin n, ∑ i ∈ I, if v ∈ H.edge i then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro v _
          simp only [degreeIn, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ i ∈ I, ∑ v : Fin n, if v ∈ H.edge i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ I, (H.edge i).card := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
      simp

theorem degreeIn_pos_iff_mem_support (H : Hypergraph n m)
    (I : Finset (Fin m)) (v : Fin n) :
    0 < H.degreeIn I v ↔ v ∈ H.support I := by
  rw [H.mem_support]
  constructor
  · intro h
    rcases Finset.card_pos.mp h with ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hiI, hvi⟩
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hiI, hvi⟩⟩

/-- Double-counting incidences: non-boundary vertices in the support have
degree at least two. -/
theorem twice_support_card_le_incidence_add_boundary
    (H : Hypergraph n m) (I : Finset (Fin m)) :
    2 * (H.support I).card ≤
      (∑ i ∈ I, (H.edge i).card) + (H.boundary I).card := by
  classical
  rw [← H.sum_degreeIn I]
  have hpoint : ∀ v ∈ H.support I,
      2 ≤ H.degreeIn I v + if v ∈ H.boundary I then 1 else 0 := by
    intro v hv
    have hpos := (H.degreeIn_pos_iff_mem_support I v).mpr hv
    by_cases hb : v ∈ H.boundary I
    · have hd := (H.mem_boundary I v).mp hb
      simp [hb, hd]
    · have hdne : H.degreeIn I v ≠ 1 := by
        intro hd
        exact hb ((H.mem_boundary I v).mpr hd)
      simp only [hb, ↓reduceIte, add_zero]
      omega
  calc
    2 * (H.support I).card = ∑ v ∈ H.support I, 2 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ H.support I,
        (H.degreeIn I v + if v ∈ H.boundary I then 1 else 0) :=
      Finset.sum_le_sum fun v hv => hpoint v hv
    _ ≤ ∑ v : Fin n,
        (H.degreeIn I v + if v ∈ H.boundary I then 1 else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro v _ _
      omega
    _ = (∑ v : Fin n, H.degreeIn I v) + (H.boundary I).card := by
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ v : Fin n, if v ∈ H.boundary I then 1 else 0) =
            ∑ v ∈ H.boundary I, 1 := by
              rw [← Finset.sum_filter]
              congr 1
              ext v
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        _ = (H.boundary I).card := by simp

theorem twice_support_card_le_uniform_incidence_add_boundary
    (H : Hypergraph n m) (hk : H.IsKUniform k) (I : Finset (Fin m)) :
    2 * (H.support I).card ≤ k * I.card + (H.boundary I).card := by
  have hsum : (∑ i ∈ I, (H.edge i).card) = k * I.card := by
    calc
      (∑ i ∈ I, (H.edge i).card) = ∑ _i ∈ I, k :=
        Finset.sum_congr rfl fun i _ => hk i
      _ = k * I.card := by simp [Nat.mul_comm]
  rw [← hsum]
  exact H.twice_support_card_le_incidence_add_boundary I

theorem support_card_le_uniform_incidence
    (H : Hypergraph n m) (hk : H.IsKUniform k) (I : Finset (Fin m)) :
    (H.support I).card ≤ k * I.card := by
  calc
    (H.support I).card ≤ ∑ i ∈ I, (H.edge i).card := by
      exact Finset.card_biUnion_le
    _ = k * I.card := by
      calc
        (∑ i ∈ I, (H.edge i).card) = ∑ _i ∈ I, k :=
          Finset.sum_congr rfl fun i _ => hk i
        _ = k * I.card := by simp [Nat.mul_comm]

theorem subset_edgesContainedIn_support
    (H : Hypergraph n m) (I : Finset (Fin m)) :
    I ⊆ H.edgesContainedIn (H.support I) := by
  intro i hi
  rw [H.mem_edgesContainedIn]
  intro v hv
  exact (H.mem_support I v).mpr ⟨i, hi, hv⟩

/-- The first conclusion of CS87 Lemma 3, at the paper's exact constant. -/
theorem propertyP_of_sparse
    (H : Hypergraph n m) (hk : H.IsKUniform k)
    (hsparse : H.IsSparse (a * k) (4 / (2 * k + 1 : ℝ))) :
    H.HasPropertyP a := by
  intro I hI
  have hsupportNat := H.support_card_le_uniform_incidence hk I
  have hsupport :
      ((H.support I).card : ℝ) ≤ (k : ℝ) * I.card := by
    exact_mod_cast hsupportNat
  have hsmall : ((H.support I).card : ℝ) ≤ (a * k) * n := by
    calc
      ((H.support I).card : ℝ) ≤ (k : ℝ) * I.card := hsupport
      _ ≤ (k : ℝ) * (a * n) := by gcongr
      _ = (a * k) * n := by ring
  have hs := hsparse (H.support I) hsmall
  have hcontained :
      (I.card : ℝ) ≤ (H.edgesContainedIn (H.support I)).card := by
    exact_mod_cast Finset.card_le_card (H.subset_edgesContainedIn_support I)
  have hlower :
      (I.card : ℝ) ≤ (4 / (2 * k + 1 : ℝ)) * (H.support I).card :=
    hcontained.trans hs
  have hincNat :=
    H.twice_support_card_le_uniform_incidence_add_boundary hk I
  have hinc :
      2 * ((H.support I).card : ℝ) ≤
        (k : ℝ) * I.card + (H.boundary I).card := by
    exact_mod_cast hincNat
  have hden : 0 < (2 * (k : ℝ) + 1) := by positivity
  by_contra h
  have hb : ((H.boundary I).card : ℝ) < (I.card : ℝ) / 2 :=
    lt_of_not_ge h
  have hmnonneg : 0 ≤ (I.card : ℝ) := by positivity
  have hlower' :
      (2 * (k : ℝ) + 1) * I.card ≤ 4 * (H.support I).card := by
    have hquot :
        (I.card : ℝ) ≤
          (4 * (H.support I).card) / (2 * (k : ℝ) + 1) := by
      convert hlower using 1
      all_goals field_simp
    have := (le_div_iff₀ hden).mp hquot
    nlinarith
  nlinarith

theorem hasSDR_iff_hall (H : Hypergraph n m) (I : Finset (Fin m)) :
    H.HasSDR I ↔
      ∀ J : Finset I, J.card ≤
        (J.biUnion fun i => H.edge i).card := by
  classical
  simpa [HasSDR] using
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun i : I => H.edge i)).symm

theorem hasSDRDisjointFrom_iff_hall (H : Hypergraph n m)
    (I : Finset (Fin m)) (D : Finset (Fin n)) :
    H.HasSDRDisjointFrom I D ↔
      ∀ J : Finset I, J.card ≤
        (J.biUnion fun i => H.edge i \ D).card := by
  classical
  rw [Finset.all_card_le_biUnion_card_iff_existsInjective']
  constructor
  · rintro ⟨f, hf, hmem, hD⟩
    exact ⟨f, hf, fun i => Finset.mem_sdiff.mpr ⟨hmem i, hD i⟩⟩
  · rintro ⟨f, hf, hmem⟩
    exact ⟨f, hf, fun i => (Finset.mem_sdiff.mp (hmem i)).1,
      fun i => (Finset.mem_sdiff.mp (hmem i)).2⟩

theorem hasSDR_of_boundary_large (H : Hypergraph n m) (I : Finset (Fin m))
    (hboundary : ∀ J : Finset (Fin m), J ⊆ I →
      J.card ≤ (H.boundary J).card) :
    H.HasSDR I := by
  rw [H.hasSDR_iff_hall]
  intro J
  let J' : Finset (Fin m) := J.image Subtype.val
  have hJI : J' ⊆ I := by
    intro i hi
    simp only [J', Finset.mem_image] at hi
    rcases hi with ⟨j, hj, rfl⟩
    exact j.property
  have hcard : J'.card = J.card :=
    Finset.card_image_of_injective J Subtype.val_injective
  calc
    J.card = J'.card := hcard.symm
    _ ≤ (H.boundary J').card := hboundary J' hJI
    _ ≤ (J.biUnion fun i => H.edge i).card := by
      apply Finset.card_le_card
      intro v hv
      have hv' : ∃ i ∈ J', v ∈ H.edge i := by
        have hd := (H.mem_boundary J' v).mp hv
        simp only [degreeIn, Finset.card_eq_one] at hd
        rcases hd with ⟨i, hi⟩
        have hii : i ∈ J' := by
          have : i ∈ J'.filter fun j => v ∈ H.edge j := by simp [hi]
          exact (Finset.mem_filter.mp this).1
        exact ⟨i, hii, by
          have : i ∈ J'.filter fun j => v ∈ H.edge j := by simp [hi]
          exact (Finset.mem_filter.mp this).2⟩
      rcases hv' with ⟨i, hiJ', hvi⟩
      simp only [J', Finset.mem_image] at hiJ'
      rcases hiJ' with ⟨j, hj, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨j, hj, hvi⟩

/-- Boundary peeling gives an SDR. This is the argument used implicitly after
CS87 (5.5); it is stronger than merely invoking cardinality of one boundary. -/
theorem hasSDR_of_subfamilies_boundary_nonempty
    (H : Hypergraph n m) (I : Finset (Fin m))
    (hpeel : ∀ J : Finset (Fin m), J ⊆ I → J.Nonempty →
      (H.boundary J).Nonempty) :
    H.HasSDR I := by
  classical
  induction hcard : I.card using Nat.strong_induction_on generalizing I with
  | h q ih =>
      by_cases hI : I.Nonempty
      · rcases hpeel I (fun _ h => h) hI with ⟨v, hv⟩
        have hdeg := (H.mem_boundary I v).mp hv
        simp only [degreeIn, Finset.card_eq_one] at hdeg
        rcases hdeg with ⟨e, he⟩
        have hefilter :
            e ∈ I.filter fun i => v ∈ H.edge i := by simp [he]
        have heI : e ∈ I := (Finset.mem_filter.mp hefilter).1
        have hve : v ∈ H.edge e := (Finset.mem_filter.mp hefilter).2
        let I' := I.erase e
        have hlt : I'.card < q := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem heI
        have hsub : I' ⊆ I := Finset.erase_subset _ _
        have hpeel' : ∀ J : Finset (Fin m), J ⊆ I' → J.Nonempty →
            (H.boundary J).Nonempty := by
          intro J hJ hJn
          exact hpeel J (hJ.trans hsub) hJn
        rcases ih I'.card hlt I' hpeel' rfl with ⟨f, hf, hfm⟩
        let g : I → Fin n := fun i =>
          if hi : i.val = e then v else f ⟨i.val, by
            exact Finset.mem_erase.mpr ⟨hi, i.property⟩⟩
        refine ⟨g, ?_, ?_⟩
        · intro i j hij
          by_cases hi : i.val = e <;> by_cases hj : j.val = e
          · exact Subtype.ext (hi.trans hj.symm)
          · exfalso
            have hvnot : v ∉ H.edge j.val := by
              intro hvj
              have hjfilter :
                  j.val ∈ I.filter fun z => v ∈ H.edge z :=
                Finset.mem_filter.mpr ⟨j.property, hvj⟩
              have := congrArg (fun s => j.val ∈ s) he
              simp only [Finset.mem_singleton] at this
              exact hj (this.mp hjfilter)
            have hfj := hfm ⟨j.val, Finset.mem_erase.mpr ⟨hj, j.property⟩⟩
            have hvf :
                v = f ⟨j.val, Finset.mem_erase.mpr ⟨hj, j.property⟩⟩ := by
              simpa [g, hi, hj] using hij
            exact hvnot (by rw [hvf]; exact hfj)
          · exfalso
            have hvnot : v ∉ H.edge i.val := by
              intro hvi
              have hifilter :
                  i.val ∈ I.filter fun z => v ∈ H.edge z :=
                Finset.mem_filter.mpr ⟨i.property, hvi⟩
              have := congrArg (fun s => i.val ∈ s) he
              simp only [Finset.mem_singleton] at this
              exact hi (this.mp hifilter)
            have hfi := hfm ⟨i.val, Finset.mem_erase.mpr ⟨hi, i.property⟩⟩
            have hfv :
                f ⟨i.val, Finset.mem_erase.mpr ⟨hi, i.property⟩⟩ = v := by
              simpa [g, hi, hj] using hij
            exact hvnot (by rw [← hfv]; exact hfi)
          · have hfij : (⟨i.val, Finset.mem_erase.mpr ⟨hi, i.property⟩⟩ : I') =
                ⟨j.val, Finset.mem_erase.mpr ⟨hj, j.property⟩⟩ := by
              apply hf
              simpa [g, hi, hj] using hij
            have hv : i.val = j.val :=
              congrArg (fun z : I' => z.val) hfij
            exact Subtype.ext hv
        · intro i
          by_cases hi : i.val = e
          · simpa [g, hi] using hve
          · simpa [g, hi] using
              hfm ⟨i.val, Finset.mem_erase.mpr ⟨hi, i.property⟩⟩
      · have hIcard : I.card = 0 :=
          Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hI)
        rw [H.hasSDR_iff_hall]
        intro J
        have hJle : J.card ≤ I.card := by
          rw [← Finset.card_image_of_injective J Subtype.val_injective]
          exact Finset.card_le_card (by
            intro i hi
            simp only [Finset.mem_image] at hi
            rcases hi with ⟨j, _, rfl⟩
            exact j.property)
        omega

theorem hasSDR_of_propertyP
    (H : Hypergraph n m) (hP : H.HasPropertyP a)
    (I : Finset (Fin m)) (hI : (I.card : ℝ) ≤ a * n) :
    H.HasSDR I := by
  apply H.hasSDR_of_subfamilies_boundary_nonempty I
  intro J hJI hJn
  have hJcard : (J.card : ℝ) ≤ a * n := by
    calc
      (J.card : ℝ) ≤ I.card := by
        exact_mod_cast Finset.card_le_card hJI
      _ ≤ a * n := hI
  have hbound := hP J hJcard
  rw [Finset.nonempty_iff_ne_empty]
  intro hb
  rw [hb] at hbound
  simp only [Finset.card_empty, Nat.cast_zero] at hbound
  have : (0 : ℝ) < J.card / 2 := by positivity
  linarith

theorem cluster_card_le_twice_set
    (H : Hypergraph n m) (hP : H.HasPropertyP a)
    (S : Finset (Fin n)) (I : Finset (Fin m))
    (hcluster : H.IsCluster S I)
    (hI : (I.card : ℝ) ≤ a * n) :
    I.card ≤ 2 * S.card := by
  have hb := hP I hI
  have hsub := Finset.card_le_card hcluster
  have hsubR : ((H.boundary I).card : ℝ) ≤ S.card := by
    exact_mod_cast hsub
  have hreal : (I.card : ℝ) ≤ 2 * S.card := by linarith
  exact_mod_cast hreal

theorem boundary_union_subset
    (H : Hypergraph n m) (I J : Finset (Fin m)) :
    H.boundary (I ∪ J) ⊆ H.boundary I ∪ H.boundary J := by
  intro v hv
  have huv := (H.mem_boundary (I ∪ J) v).mp hv
  change ((I ∪ J).filter fun i => v ∈ H.edge i).card = 1 at huv
  have hfilter :
      (I ∪ J).filter (fun i => v ∈ H.edge i) =
        I.filter (fun i => v ∈ H.edge i) ∪
          J.filter (fun i => v ∈ H.edge i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  rw [hfilter] at huv
  by_cases hvi : H.degreeIn I v = 1
  · exact Finset.mem_union_left _ ((H.mem_boundary I v).mpr hvi)
  · by_cases hvj : H.degreeIn J v = 1
    · exact Finset.mem_union_right _ ((H.mem_boundary J v).mpr hvj)
    · have hIle : H.degreeIn I v ≤ 1 := by
        change (I.filter fun i => v ∈ H.edge i).card ≤ 1
        have hsub :
            I.filter (fun i => v ∈ H.edge i) ⊆
              I.filter (fun i => v ∈ H.edge i) ∪
                J.filter (fun i => v ∈ H.edge i) :=
          Finset.subset_union_left
        calc
          _ ≤ (I.filter (fun i => v ∈ H.edge i) ∪
                J.filter (fun i => v ∈ H.edge i)).card :=
            Finset.card_le_card hsub
          _ = 1 := huv
      have hJle : H.degreeIn J v ≤ 1 := by
        change (J.filter fun i => v ∈ H.edge i).card ≤ 1
        have hsub :
            J.filter (fun i => v ∈ H.edge i) ⊆
              I.filter (fun i => v ∈ H.edge i) ∪
                J.filter (fun i => v ∈ H.edge i) :=
          Finset.subset_union_right
        calc
          _ ≤ (I.filter (fun i => v ∈ H.edge i) ∪
                J.filter (fun i => v ∈ H.edge i)).card :=
            Finset.card_le_card hsub
          _ = 1 := huv
      have hIzero : H.degreeIn I v = 0 := by omega
      have hJzero : H.degreeIn J v = 0 := by omega
      have hIe : I.filter (fun i => v ∈ H.edge i) = ∅ := by
        exact Finset.card_eq_zero.mp hIzero
      have hJe : J.filter (fun i => v ∈ H.edge i) = ∅ := by
        exact Finset.card_eq_zero.mp hJzero
      rw [hIe, hJe] at huv
      simp at huv

theorem cluster_union
    (H : Hypergraph n m) (S : Finset (Fin n)) (I J : Finset (Fin m))
    (hI : H.IsCluster S I) (hJ : H.IsCluster S J) :
    H.IsCluster S (I ∪ J) :=
  (H.boundary_union_subset I J).trans
    (Finset.union_subset hI hJ)

end Hypergraph

/-- Ordered `k`-uniform hypergraphs: edge coordinates are independent trials,
and equal edge values at distinct coordinates are not identified. -/
abbrev OrderedKUniformHypergraph (n m k : Nat) :=
  Fin m → ClauseVariables n k

def OrderedKUniformHypergraph.toHypergraph
    (G : OrderedKUniformHypergraph n m k) : Hypergraph n m where
  edge i := (G i).val

theorem OrderedKUniformHypergraph.toHypergraph_isKUniform
    (G : OrderedKUniformHypergraph n m k) :
    G.toHypergraph.IsKUniform k := fun i => (G i).property

/-- CS87's random ordered `k`-uniform hypergraph with `n` vertices and `m`
independent uniformly sampled edges. -/
noncomputable def randomOrderedKUniformHypergraph (n m k : Nat)
    [Nonempty (ClauseVariables n k)] :
    FinitePMF (OrderedKUniformHypergraph n m k) :=
  FinitePMF.uniform (OrderedKUniformHypergraph n m k)

noncomputable def randomOrderedKUniformHypergraphOfLE
    (n m k : Nat) (hk : k ≤ n) :
    FinitePMF (OrderedKUniformHypergraph n m k) := by
  let C := positiveOrdinaryClause hk
  letI : Nonempty (ClauseVariables n k) := ⟨C.1⟩
  exact randomOrderedKUniformHypergraph n m k

@[simp] theorem orderedKUniformHypergraph_cardinality :
    Fintype.card (OrderedKUniformHypergraph n m k) = (n.choose k) ^ m := by
  rw [Fintype.card_fun, Fintype.card_fin, clauseVariables_card]

def clauseHypergraph (F : OrdinaryCNF n m k) : Hypergraph n m where
  edge := fun i => (F i).varSet

theorem clauseHypergraph_kUniform (F : OrdinaryCNF n m k) :
    (clauseHypergraph F).IsKUniform k := by
  intro i
  exact (F i).varSet_card

/-- Forget signs. This is exactly the ordered edge projection used in CS87. -/
def projectRandomCNF (F : OrdinaryCNF n m k) : Hypergraph n m :=
  clauseHypergraph F

@[simp] theorem projectRandomCNF_edge (F : OrdinaryCNF n m k) (i : Fin m) :
    (projectRandomCNF F).edge i = (F i).varSet := rfl

end AvgCaseMls.Section3
