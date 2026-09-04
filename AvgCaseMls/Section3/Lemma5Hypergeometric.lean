import AvgCaseMls.Section3.Lemma5Counting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# CS87 Lemma 5: the finite hypergeometric estimate

This file isolates the unconditional finite arithmetic behind equation (6.4).
The summand below is the number of `s`-subsets having intersection `j` with a
fixed `m`-subset of an `n`-set.
-/

namespace AvgCaseMls.Section3

open scoped BigOperators

/-- A finite decreasing tilt can only lower a weighted mean.  This is the
pairwise sum-of-squares (Chebyshev covariance) argument, stated without
division so zero total weight causes no exceptional case. -/
theorem sum_mul_sum_id_mul_le
    (S : Finset Nat) (w f : Nat → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i)
    (hf : Antitone f) :
    (∑ i ∈ S, w i) * (∑ i ∈ S, w i * i * f i) ≤
      (∑ i ∈ S, w i * i) * (∑ i ∈ S, w i * f i) := by
  have hp : ∀ i ∈ S, ∀ j ∈ S,
      0 ≤ w i * w j * ((i : ℝ) - (j : ℝ)) * (f j - f i) := by
    intro i hi j hj
    have hwij : 0 ≤ w i * w j := mul_nonneg (hw i hi) (hw j hj)
    rcases le_total i j with hij | hji
    · have hd₁ : (i : ℝ) - (j : ℝ) ≤ 0 :=
        sub_nonpos.mpr (Nat.cast_le.mpr hij)
      have hd₂ : f j - f i ≤ 0 := sub_nonpos.mpr (hf hij)
      calc
        0 ≤ (w i * w j) * (((i : ℝ) - j) * (f j - f i)) :=
          mul_nonneg hwij (mul_nonneg_of_nonpos_of_nonpos hd₁ hd₂)
        _ = w i * w j * ((i : ℝ) - j) * (f j - f i) := by ring
    · have hd₁ : 0 ≤ (i : ℝ) - (j : ℝ) :=
        sub_nonneg.mpr (Nat.cast_le.mpr hji)
      have hd₂ : 0 ≤ f j - f i := sub_nonneg.mpr (hf hji)
      calc
        0 ≤ (w i * w j) * (((i : ℝ) - j) * (f j - f i)) :=
          mul_nonneg hwij (mul_nonneg hd₁ hd₂)
        _ = w i * w j * ((i : ℝ) - j) * (f j - f i) := by ring
  have hsum :
      0 ≤ ∑ i ∈ S, ∑ j ∈ S,
        w i * w j * ((i : ℝ) - j) * (f j - f i) :=
    Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => hp i hi j hj
  have hswap :
      (∑ i ∈ S, ∑ j ∈ S, w i * w j * (i : ℝ) * f j) =
        ∑ i ∈ S, ∑ j ∈ S, w i * w j * (j : ℝ) * f i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hA :
      (∑ i ∈ S, ∑ j ∈ S, w i * w j * (i : ℝ) * f j) =
        (∑ i ∈ S, w i * i) * (∑ i ∈ S, w i * f i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hB :
      (∑ i ∈ S, ∑ j ∈ S, w i * w j * (i : ℝ) * f i) =
        (∑ i ∈ S, w i) * (∑ i ∈ S, w i * i * f i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hC :
      (∑ i ∈ S, ∑ j ∈ S, w i * w j * (j : ℝ) * f j) =
        (∑ i ∈ S, w i) * (∑ i ∈ S, w i * i * f i) := by
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hE :
      (∑ i ∈ S, ∑ j ∈ S,
          w i * w j * ((i : ℝ) - j) * (f j - f i)) =
        2 * ((∑ i ∈ S, w i * i) * (∑ i ∈ S, w i * f i) -
          (∑ i ∈ S, w i) * (∑ i ∈ S, w i * i * f i)) := by
    calc
      (∑ i ∈ S, ∑ j ∈ S,
          w i * w j * ((i : ℝ) - j) * (f j - f i)) =
          (∑ i ∈ S, ∑ j ∈ S, w i * w j * (i : ℝ) * f j) -
          (∑ i ∈ S, ∑ j ∈ S, w i * w j * (i : ℝ) * f i) -
          (∑ i ∈ S, ∑ j ∈ S, w i * w j * (j : ℝ) * f j) +
          (∑ i ∈ S, ∑ j ∈ S, w i * w j * (j : ℝ) * f i) := by
            simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
            ring
      _ = 2 * ((∑ i ∈ S, w i * i) * (∑ i ∈ S, w i * f i) -
          (∑ i ∈ S, w i) * (∑ i ∈ S, w i * i * f i)) := by
            rw [hA, hB, hC, ← hswap, hA]
            ring
  rw [hE] at hsum
  linarith

/-- The unnormalised hypergeometric mass at `j`. -/
def hypergeomCount (n m s j : Nat) : Nat :=
  m.choose j * (n - m).choose (s - j)

/-- The lower-tail numerator occurring immediately before CS87 (6.4). -/
def hypergeomLowerCount (n m s t : Nat) : Nat :=
  ∑ j ∈ Finset.range (t + 1), hypergeomCount n m s j

/-- The exact floor-free lower tail used by CS87: because `j` is natural,
the real comparison in the filter incorporates the required floor. -/
noncomputable def hypergeomLowerCountReal
    (n m s : Nat) (r : ℝ) : Nat :=
  ∑ j ∈ (Finset.range (s + 1)).filter fun j : Nat => (j : ℝ) ≤ r,
    hypergeomCount n m s j

/-- Exact enumeration of `s`-sets having `j` points in a fixed set. -/
theorem card_powersetCard_filter_inter_card
    (E : Finset (Fin n)) {s j : Nat} (hjs : j ≤ s) :
    (((Finset.univ : Finset (Fin n)).powersetCard s).filter
      fun S => (S ∩ E).card = j).card =
        hypergeomCount n E.card s j := by
  classical
  let U : Finset (Fin n) := Finset.univ \ E
  let A := E.powersetCard j
  let B := U.powersetCard (s - j)
  let P := A ×ˢ B
  have hEuniv : E ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
  have hUcard : U.card = n - E.card := by
    simp [U, Finset.card_sdiff_of_subset hEuniv]
  have hcard :
      (((Finset.univ : Finset (Fin n)).powersetCard s).filter
        fun S => (S ∩ E).card = j).card = P.card := by
    apply Finset.card_bij (fun S _ => (S ∩ E, S \ E))
    · intro S hS
      have hs := Finset.mem_filter.mp hS
      have hsΩ := Finset.mem_powersetCard.mp hs.1
      simp only [P, Finset.mem_product, A, B, Finset.mem_powersetCard]
      refine ⟨⟨Finset.inter_subset_right, hs.2⟩, ?_⟩
      refine ⟨?_, ?_⟩
      · intro x hx
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
      · rw [Finset.card_sdiff, Finset.inter_comm, hs.2, hsΩ.2]
    · intro S₁ hS₁ S₂ hS₂ heq
      have h₁ : S₁ ∩ E = S₂ ∩ E := congrArg Prod.fst heq
      have h₂ : S₁ \ E = S₂ \ E := congrArg Prod.snd heq
      ext x
      by_cases hxE : x ∈ E
      · have hi₁ : x ∈ S₁ ↔ x ∈ S₁ ∩ E := by simp [hxE]
        have hi₂ : x ∈ S₂ ↔ x ∈ S₂ ∩ E := by simp [hxE]
        rw [hi₁, h₁, ← hi₂]
      · have hd₁ : x ∈ S₁ ↔ x ∈ S₁ \ E := by simp [hxE]
        have hd₂ : x ∈ S₂ ↔ x ∈ S₂ \ E := by simp [hxE]
        rw [hd₁, h₂, ← hd₂]
    · intro p hp
      rcases p with ⟨X, Y⟩
      simp only [P, Finset.mem_product, A, B,
        Finset.mem_powersetCard] at hp
      have hXY : Disjoint X Y := by
        rw [Finset.disjoint_left]
        intro x hxX hxY
        exact (Finset.mem_sdiff.mp (hp.2.1 hxY)).2 (hp.1.1 hxX)
      have hYE : Disjoint Y E := by
        rw [Finset.disjoint_left]
        intro x hxY hxE
        exact (Finset.mem_sdiff.mp (hp.2.1 hxY)).2 hxE
      refine ⟨X ∪ Y, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_powersetCard.mpr
          refine ⟨Finset.union_subset
            (hp.1.1.trans (Finset.subset_univ E))
            (hp.2.1.trans Finset.sdiff_subset), ?_⟩
          rw [Finset.card_union_of_disjoint hXY, hp.1.2, hp.2.2]
          exact Nat.add_sub_of_le hjs
        · rw [Finset.union_inter_distrib_right,
            Finset.inter_eq_left.mpr hp.1.1,
            (Finset.disjoint_iff_inter_eq_empty.mp hYE),
            Finset.union_empty, hp.1.2]
      · apply Prod.ext
        · simp only [Prod.fst]
          rw [Finset.union_inter_distrib_right,
            Finset.inter_eq_left.mpr hp.1.1,
            (Finset.disjoint_iff_inter_eq_empty.mp hYE), Finset.union_empty]
        · simp only [Prod.snd]
          rw [Finset.union_sdiff_distrib,
            Finset.sdiff_eq_empty_iff_subset.mpr hp.1.1,
            Finset.sdiff_eq_self_iff_disjoint.mpr hYE, Finset.empty_union]
  rw [hcard, Finset.card_product, Finset.card_powersetCard,
    Finset.card_powersetCard, hUcard]
  rfl

/-- Exact lower-tail enumeration for a fixed distinguished set. -/
theorem card_powersetCard_filter_inter_le
    (E : Finset (Fin n)) (s : Nat) (r : ℝ) :
    (((Finset.univ : Finset (Fin n)).powersetCard s).filter
      fun S => ((S ∩ E).card : ℝ) ≤ r).card =
        hypergeomLowerCountReal n E.card s r := by
  classical
  let Ω := (Finset.univ : Finset (Fin n)).powersetCard s
  let J := (Finset.range (s + 1)).filter fun j : Nat => (j : ℝ) ≤ r
  calc
    (Ω.filter fun S => ((S ∩ E).card : ℝ) ≤ r).card =
        ∑ j ∈ J, (Ω.filter fun S => (S ∩ E).card = j).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext S
        constructor
        · intro hS
          have hS' := Finset.mem_filter.mp hS
          have hScard := (Finset.mem_powersetCard.mp hS'.1).2
          apply Finset.mem_biUnion.mpr
          refine ⟨(S ∩ E).card, ?_, ?_⟩
          · apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_range.mpr ?_, hS'.2⟩
            have := Finset.card_le_card
              (Finset.inter_subset_left : S ∩ E ⊆ S)
            omega
          · exact Finset.mem_filter.mpr ⟨hS'.1, rfl⟩
        · intro hS
          rcases Finset.mem_biUnion.mp hS with ⟨j, hj, hSj⟩
          have hj' := Finset.mem_filter.mp hj
          have hSj' := Finset.mem_filter.mp hSj
          exact Finset.mem_filter.mpr
            ⟨hSj'.1, by rw [hSj'.2]; exact hj'.2⟩
      · intro i hi j hj hij
        change Disjoint
          (Ω.filter fun S => (S ∩ E).card = i)
          (Ω.filter fun S => (S ∩ E).card = j)
        rw [Finset.disjoint_left]
        intro S hSi hSj
        have hSi' := (Finset.mem_filter.mp hSi).2
        have hSj' := (Finset.mem_filter.mp hSj).2
        exact hij (hSi'.symm.trans hSj')
    _ = ∑ j ∈ J, hypergeomCount n E.card s j := by
      apply Finset.sum_congr rfl
      intro j hj
      apply card_powersetCard_filter_inter_card E
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
    _ = hypergeomLowerCountReal n E.card s r := by
      rfl

/-- Exact factorial cancellation for one nonzero hypergeometric summand. -/
theorem hypergeomCount_mul_factorials
    {n m s j : Nat} (hjm : j ≤ m)
    (hsj : s - j ≤ n - m) :
    hypergeomCount n m s j * j.factorial * (m - j).factorial *
          (s - j).factorial * (n - m - (s - j)).factorial =
      m.factorial * (n - m).factorial := by
  rw [hypergeomCount]
  have hm :=
    Nat.choose_mul_factorial_mul_factorial hjm
  have hnm :=
    Nat.choose_mul_factorial_mul_factorial hsj
  calc
    m.choose j * (n - m).choose (s - j) * j.factorial *
          (m - j).factorial * (s - j).factorial *
          (n - m - (s - j)).factorial =
        (m.choose j * j.factorial * (m - j).factorial) *
          ((n - m).choose (s - j) * (s - j).factorial *
            (n - m - (s - j)).factorial) := by ring
    _ = m.factorial * (n - m).factorial := by rw [hm, hnm]

/-- A hypergeometric summand vanishes when too many points are requested
from the distinguished part. -/
theorem hypergeomCount_eq_zero_of_m_lt_j
    {n m s j : Nat} (h : m < j) :
    hypergeomCount n m s j = 0 := by
  simp [hypergeomCount, Nat.choose_eq_zero_of_lt h]

/-- A hypergeometric summand vanishes when too many points are requested
from the complement. -/
theorem hypergeomCount_eq_zero_of_compl_lt
    {n m s j : Nat} (h : n - m < s - j) :
    hypergeomCount n m s j = 0 := by
  simp [hypergeomCount, Nat.choose_eq_zero_of_lt h]

/-- Vandermonde's identity in the indexing used by `hypergeomCount`. -/
theorem sum_hypergeomCount
    {n m s : Nat} (hmn : m ≤ n) :
    ∑ j ∈ Finset.range (s + 1), hypergeomCount n m s j =
      n.choose s := by
  calc
    ∑ j ∈ Finset.range (s + 1), hypergeomCount n m s j =
        (m + (n - m)).choose s := by
      rw [Nat.add_choose_eq,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      rfl
    _ = n.choose s := by rw [Nat.add_sub_of_le hmn]

/-- The first-moment form of Vandermonde's identity. -/
theorem sum_id_mul_hypergeomCount
    {n m s : Nat} (hmn : m ≤ n) :
    n * (∑ j ∈ Finset.range (s + 1), j * hypergeomCount n m s j) =
      m * s * n.choose s := by
  by_cases hm : m = 0
  · subst m
    simp only [Nat.zero_mul]
    have hz :
        (∑ j ∈ Finset.range (s + 1), j * hypergeomCount n 0 s j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      cases j with
      | zero => simp
      | succ j => simp [hypergeomCount]
    rw [hz, Nat.mul_zero]
  by_cases hs : s = 0
  · subst s
    simp
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hspos : 0 < s := Nat.pos_of_ne_zero hs
  have hmn' : m - 1 + (n - m) = n - 1 := by omega
  have hsum :
      (∑ j ∈ Finset.range (s + 1), j * hypergeomCount n m s j) =
        m * (n - 1).choose (s - 1) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.zero_mul]
    calc
      (∑ j ∈ Finset.range s, (j + 1) * hypergeomCount n m s (j + 1)) =
          ∑ j ∈ Finset.range s,
            m * ((m - 1).choose j * (n - m).choose ((s - 1) - j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjs : j < s := Finset.mem_range.mp hj
        have hchoose := Nat.choose_mul (n := m) (k := j + 1) (s := 1)
          (by omega : 1 ≤ j + 1)
        simp only [Nat.choose_one_right, Nat.add_sub_cancel, Nat.mul_comm] at hchoose
        rw [hypergeomCount]
        rw [← Nat.mul_assoc, hchoose]
        have hsub : s - (j + 1) = (s - 1) - j := by omega
        rw [hsub]
        rw [Nat.mul_assoc]
      _ = m * ∑ j ∈ Finset.range s,
            (m - 1).choose j * (n - m).choose ((s - 1) - j) := by
        rw [Finset.mul_sum]
      _ = m * (n - 1).choose (s - 1) := by
        have hs_eq : s = (s - 1) + 1 := (Nat.sub_add_cancel hspos).symm
        rw [← hmn', Nat.add_choose_eq,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        congr 3
  rw [hsum]
  have hchoose := Nat.choose_mul (n := n) (k := s) (s := 1)
    (by omega : 1 ≤ s)
  simp only [Nat.choose_one_right, Nat.mul_comm] at hchoose
  calc
    n * (m * (n - 1).choose (s - 1)) =
        m * (n * (n - 1).choose (s - 1)) := by ac_rfl
    _ = m * (s * n.choose s) := by rw [hchoose]
    _ = m * s * n.choose s := by rw [Nat.mul_assoc]

/-- The unnormalised probability generating function. -/
noncomputable def hypergeomPGF (n m s : Nat) (q : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (s + 1), q ^ j * hypergeomCount n m s j

/-- Tilting by `q^j`, for `q ≤ 1`, lowers the hypergeometric first moment. -/
theorem hypergeom_tilted_mean_le
    {n m s : Nat} {q : ℝ} (hn : 0 < n) (hmn : m ≤ n)
    (hsn : s ≤ n) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (n : ℝ) * (∑ j ∈ Finset.range (s + 1),
        (j : ℝ) * (hypergeomCount n m s j : ℝ) * q ^ j) ≤
      (m : ℝ) * s * hypergeomPGF n m s q := by
  let S := Finset.range (s + 1)
  let w : Nat → ℝ := fun j => hypergeomCount n m s j
  let f : Nat → ℝ := fun j => q ^ j
  have hf : Antitone f := by
    intro i j hij
    exact pow_le_pow_of_le_one hq0 hq1 hij
  have hc := sum_mul_sum_id_mul_le S w f
    (fun i hi => Nat.cast_nonneg _) hf
  have htotal :
      (∑ j ∈ S, w j) = (n.choose s : ℝ) := by
    simp only [S, w, ← Nat.cast_sum]
    rw [sum_hypergeomCount hmn]
  have hmoment :
      (n : ℝ) * (∑ j ∈ S, w j * j) =
        (m : ℝ) * s * (n.choose s : ℝ) := by
    have hnat :=
      sum_id_mul_hypergeomCount (n := n) (m := m) (s := s) hmn
    have hcast :
        ((n * (∑ j ∈ Finset.range (s + 1),
            j * hypergeomCount n m s j) : Nat) : ℝ) =
          ((m * s * n.choose s : Nat) : ℝ) := by exact_mod_cast hnat
    simpa only [S, w, Nat.cast_mul, Nat.cast_sum, mul_comm] using hcast
  have hchoose : 0 < (n.choose s : ℝ) := by
    exact_mod_cast Nat.choose_pos hsn
  rw [htotal] at hc
  have hscaled := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ n by positivity)
  have hscaled' :
      (n.choose s : ℝ) * ((n : ℝ) * ∑ i ∈ S, w i * i * f i) ≤
        ((m : ℝ) * s * (n.choose s : ℝ)) * ∑ i ∈ S, w i * f i := by
    calc
      (n.choose s : ℝ) * ((n : ℝ) * ∑ i ∈ S, w i * i * f i) =
          (n : ℝ) * ((n.choose s : ℝ) * ∑ i ∈ S, w i * i * f i) := by ring
      _ ≤ (n : ℝ) * ((∑ i ∈ S, w i * i) * ∑ i ∈ S, w i * f i) :=
        hscaled
      _ = ((n : ℝ) * ∑ i ∈ S, w i * i) * ∑ i ∈ S, w i * f i := by ring
      _ = ((m : ℝ) * s * (n.choose s : ℝ)) * ∑ i ∈ S, w i * f i := by
        rw [hmoment]
  dsimp [S, w, f, hypergeomPGF] at hscaled ⊢
  have hcancel :
      (n.choose s : ℝ) *
          ((n : ℝ) * ∑ j ∈ Finset.range (s + 1),
            (j : ℝ) * hypergeomCount n m s j * q ^ j) ≤
        (n.choose s : ℝ) *
          ((m : ℝ) * s * ∑ j ∈ Finset.range (s + 1),
            q ^ j * hypergeomCount n m s j) := by
    dsimp [S, w, f] at hscaled'
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hscaled'
  nlinarith [hcancel, hchoose]

/-- Counting all one-point extensions of a weighted subset. -/
theorem hypergeomPGF_succ
    {n m s : Nat} (hmn : m ≤ n) (hsn : s < n) (q : ℝ) :
    ((s + 1 : Nat) : ℝ) * hypergeomPGF n m (s + 1) q =
      ∑ j ∈ Finset.range (s + 1), q ^ j * hypergeomCount n m s j *
        (((m - j : Nat) : ℝ) * q + ((n - m - (s - j) : Nat) : ℝ)) := by
  let c := n - m
  have hsc : s + 1 ≤ m + c := by
    dsimp [c]
    rw [Nat.add_sub_of_le hmn]
    omega
  rw [hypergeomPGF, Finset.mul_sum]
  have hsplit :
      (∑ k ∈ Finset.range (s + 2),
          ((s + 1 : Nat) : ℝ) * (q ^ k * hypergeomCount n m (s + 1) k)) =
        (∑ k ∈ Finset.range (s + 2),
          (k : ℝ) * (q ^ k * hypergeomCount n m (s + 1) k)) +
        ∑ k ∈ Finset.range (s + 2),
          (((s + 1 - k : Nat) : ℝ) *
            (q ^ k * hypergeomCount n m (s + 1) k)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hks : k ≤ s + 1 := by
      have := Finset.mem_range.mp hk
      omega
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hks]
    ring
  rw [hsplit]
  have hsuccess :
      (∑ k ∈ Finset.range (s + 2),
          (k : ℝ) * (q ^ k * hypergeomCount n m (s + 1) k)) =
        ∑ j ∈ Finset.range (s + 1),
          q ^ j * hypergeomCount n m s j * (((m - j : Nat) : ℝ) * q) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hjs : j ≤ s := by
      have := Finset.mem_range.mp hj
      omega
    have hmchoose := Nat.choose_succ_right_eq m j
    rw [hypergeomCount, hypergeomCount]
    have hsub : s + 1 - (j + 1) = s - j := by omega
    rw [hsub, pow_succ]
    have hmchooseR := congrArg (fun x : Nat => (x : ℝ)) hmchoose
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hmchooseR
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc
      ((j : ℝ) + 1) *
          (q ^ j * q * ((m.choose (j + 1) : ℝ) *
            ((n - m).choose (s - j) : ℝ))) =
          q ^ j * ((n - m).choose (s - j) : ℝ) *
            ((m.choose (j + 1) : ℝ) * (j + 1)) * q := by ring
      _ = q ^ j * ((n - m).choose (s - j) : ℝ) *
            ((m.choose j : ℝ) * ((m - j : Nat) : ℝ)) * q := by rw [hmchooseR]
      _ = q ^ j * ((m.choose j : ℝ) *
          ((n - m).choose (s - j) : ℝ)) * ((m - j : Nat) : ℝ) * q := by ring
      _ = q ^ j * ((m.choose j : ℝ) *
          ((n - m).choose (s - j) : ℝ)) * (((m - j : Nat) : ℝ) * q) := by ring
      _ = q ^ j * (hypergeomCount n m s j : ℝ) *
          (((m - j : Nat) : ℝ) * q) := by
        rw [hypergeomCount, Nat.cast_mul]
  have hordinary :
      (∑ k ∈ Finset.range (s + 2),
          (((s + 1 - k : Nat) : ℝ) *
            (q ^ k * hypergeomCount n m (s + 1) k))) =
        ∑ j ∈ Finset.range (s + 1),
          q ^ j * hypergeomCount n m s j *
            ((n - m - (s - j) : Nat) : ℝ) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hjs : j ≤ s := by
      have := Finset.mem_range.mp hj
      omega
    have hcchoose := Nat.choose_succ_right_eq (n - m) (s - j)
    rw [hypergeomCount, hypergeomCount]
    have hsub : s + 1 - j = (s - j) + 1 := by omega
    rw [hsub]
    have hcchooseR := congrArg (fun x : Nat => (x : ℝ)) hcchoose
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hcchooseR
    rw [Nat.cast_sub hjs] at hcchooseR
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [Nat.cast_sub hjs]
    calc
      ((s : ℝ) - (j : ℝ) + 1) *
          (q ^ j * ((m.choose j : ℝ) *
            ((n - m).choose ((s - j) + 1) : ℝ))) =
          q ^ j * (m.choose j : ℝ) *
            (((n - m).choose ((s - j) + 1) : ℝ) * ((s - j) + 1)) := by ring
      _ = q ^ j * (m.choose j : ℝ) *
            (((n - m).choose (s - j) : ℝ) *
              ((n - m - (s - j) : Nat) : ℝ)) := by rw [hcchooseR]
      _ = q ^ j * ((m.choose j : ℝ) *
          ((n - m).choose (s - j) : ℝ)) *
            ((n - m - (s - j) : Nat) : ℝ) := by ring
      _ = q ^ j * (hypergeomCount n m s j : ℝ) *
            ((n - m - (s - j) : Nat) : ℝ) := by
        rw [hypergeomCount, Nat.cast_mul]
  rw [hsuccess, hordinary, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The extension recurrence rewritten in terms of the tilted first moment. -/
theorem hypergeomPGF_succ_linear
    {n m s : Nat} (hmn : m ≤ n) (hsn : s < n) (q : ℝ) :
    ((s + 1 : Nat) : ℝ) * hypergeomPGF n m (s + 1) q =
      ((n - s : Nat) : ℝ) * hypergeomPGF n m s q -
        (1 - q) * ((m : ℝ) * hypergeomPGF n m s q -
          ∑ j ∈ Finset.range (s + 1),
            (j : ℝ) * (hypergeomCount n m s j : ℝ) * q ^ j) := by
  rw [hypergeomPGF_succ hmn hsn]
  dsimp [hypergeomPGF]
  simp only [Finset.mul_sum]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hc : hypergeomCount n m s j = 0
  · simp [hc]
  have hcparts :
      m.choose j ≠ 0 ∧ (n - m).choose (s - j) ≠ 0 := by
    rw [hypergeomCount] at hc
    exact (Nat.mul_ne_zero_iff).mp hc
  have hjm : j ≤ m := Nat.choose_ne_zero_iff.mp hcparts.1
  have hsj : s - j ≤ n - m := Nat.choose_ne_zero_iff.mp hcparts.2
  have hjs : j ≤ s := by
    have := Finset.mem_range.mp hj
    omega
  have hsnle : s ≤ n := Nat.le_of_lt hsn
  have harith :
      ((m - j : Nat) : ℝ) + ((n - m - (s - j) : Nat) : ℝ) =
        ((n - s : Nat) : ℝ) := by
    norm_cast
    omega
  rw [Nat.cast_sub hjm, Nat.cast_sub hsj, Nat.cast_sub hmn,
    Nat.cast_sub hjs, Nat.cast_sub hsnle]
  ring

/-- Sampling the `0/1` population without replacement has no larger
probability generating function than independent sampling with replacement. -/
theorem weighted_vandermonde_le
    (n m s : Nat) {q : ℝ} (hn : 0 < n) (hmn : m ≤ n)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    hypergeomPGF n m s q ≤
      (n.choose s : ℝ) *
        (1 - (m : ℝ) / n * (1 - q)) ^ s := by
  let a : ℝ := 1 - (m : ℝ) / n * (1 - q)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have ha0 : 0 ≤ a := by
    dsimp [a]
    rw [div_mul_eq_mul_div]
    rw [show 1 - (m : ℝ) * (1 - q) / n =
      ((n : ℝ) - m + m * q) / n by field_simp <;> ring]
    positivity
  induction s with
  | zero =>
      simp [hypergeomPGF, hypergeomCount]
  | succ s ih =>
      by_cases hsn : s < n
      · have hsle : s ≤ n := Nat.le_of_lt hsn
        have hrec := hypergeomPGF_succ_linear
          (n := n) (m := m) (s := s) hmn hsn q
        have ht := hypergeom_tilted_mean_le
          (n := n) (m := m) (s := s) hn hmn hsle hq0 hq1
        have hz : 0 ≤ 1 - q := sub_nonneg.mpr hq1
        have htz := mul_le_mul_of_nonneg_left ht hz
        have hstep :
            (n : ℝ) * (s + 1) * hypergeomPGF n m (s + 1) q ≤
              ((n - s : Nat) : ℝ) *
                ((n : ℝ) - (m : ℝ) * (1 - q)) *
                  hypergeomPGF n m s q := by
          rw [Nat.cast_sub hsle] at hrec ⊢
          norm_num only [Nat.cast_add, Nat.cast_one] at hrec
          calc
            (n : ℝ) * (s + 1) * hypergeomPGF n m (s + 1) q =
                (n : ℝ) * ((n : ℝ) - s) * hypergeomPGF n m s q -
                  (n : ℝ) * (1 - q) * (m : ℝ) *
                    hypergeomPGF n m s q +
                  (1 - q) * ((n : ℝ) *
                    ∑ j ∈ Finset.range (s + 1),
                      (j : ℝ) * hypergeomCount n m s j * q ^ j) := by
              calc
                (n : ℝ) * (s + 1) * hypergeomPGF n m (s + 1) q =
                    (n : ℝ) * ((s + 1) *
                      hypergeomPGF n m (s + 1) q) := by ring
                _ = (n : ℝ) * (((n : ℝ) - s) *
                      hypergeomPGF n m s q -
                    (1 - q) * ((m : ℝ) * hypergeomPGF n m s q -
                      ∑ j ∈ Finset.range (s + 1),
                        (j : ℝ) * hypergeomCount n m s j * q ^ j)) := by
                          rw [hrec]
                _ = _ := by ring
            _ ≤ (n : ℝ) * ((n : ℝ) - s) * hypergeomPGF n m s q -
                  (n : ℝ) * (1 - q) * (m : ℝ) *
                    hypergeomPGF n m s q +
                  (1 - q) * ((m : ℝ) * s *
                    hypergeomPGF n m s q) := by linarith
            _ = ((n : ℝ) - s) *
                ((n : ℝ) - (m : ℝ) * (1 - q)) *
                  hypergeomPGF n m s q := by ring
        have hfactor : (n : ℝ) - (m : ℝ) * (1 - q) = n * a := by
          dsimp [a]
          field_simp
        rw [hfactor] at hstep
        rw [Nat.cast_sub hsle] at hstep
        have hns0 : 0 ≤ (n : ℝ) - s := sub_nonneg.mpr (by exact_mod_cast hsle)
        have ih' : hypergeomPGF n m s q ≤ (n.choose s : ℝ) * a ^ s := by
          simpa [a] using ih
        have hchoose := Nat.choose_succ_right_eq n s
        have hchooseR := congrArg (fun x : Nat => (x : ℝ)) hchoose
        simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hchooseR
        have hnsp : (0 : ℝ) < n * (s + 1) := by positivity
        have hfinal :
            (n * (s + 1 : ℝ)) * hypergeomPGF n m (s + 1) q ≤
              (n * (s + 1 : ℝ)) *
                ((n.choose (s + 1) : ℝ) * a ^ (s + 1)) := by
          calc
          (n * (s + 1 : ℝ)) * hypergeomPGF n m (s + 1) q ≤
              ((n : ℝ) - s) * (n * a) * hypergeomPGF n m s q := by
                simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hstep
          _ ≤ ((n : ℝ) - s) * (n * a) *
              ((n.choose s : ℝ) * a ^ s) := by
                exact mul_le_mul_of_nonneg_left ih'
                  (mul_nonneg hns0 (mul_nonneg (le_of_lt hnR) ha0))
          _ = (n * (s + 1 : ℝ)) *
              ((n.choose (s + 1) : ℝ) * a ^ (s + 1)) := by
                rw [pow_succ]
                rw [Nat.cast_sub hsle] at hchooseR
                calc
                  ((n : ℝ) - s) * (n * a) *
                      ((n.choose s : ℝ) * (a ^ s)) =
                      (n : ℝ) * a ^ s * a *
                        ((n.choose s : ℝ) * ((n : ℝ) - s)) := by ring
                  _ = (n : ℝ) * a ^ s * a *
                        ((n.choose (s + 1) : ℝ) * (s + 1)) := by
                          rw [← hchooseR]
                  _ = (n * (s + 1 : ℝ)) *
                        ((n.choose (s + 1) : ℝ) * (a ^ s * a)) := by ring
        nlinarith [hfinal, hnsp]
      · have hsn' : n < s + 1 := by omega
        have hchoose0 : n.choose (s + 1) = 0 :=
          Nat.choose_eq_zero_of_lt hsn'
        have hpgf0 : hypergeomPGF n m (s + 1) q = 0 := by
          rw [hypergeomPGF]
          apply Finset.sum_eq_zero
          intro j hj
          have hjs : j ≤ s + 1 := by
            have := Finset.mem_range.mp hj
            omega
          have hc0 : hypergeomCount n m (s + 1) j = 0 := by
            by_contra hc
            have hcparts : m.choose j ≠ 0 ∧
                (n - m).choose (s + 1 - j) ≠ 0 := by
              rw [hypergeomCount] at hc
              exact (Nat.mul_ne_zero_iff).mp hc
            have hjm := Nat.choose_ne_zero_iff.mp hcparts.1
            have hcomp := Nat.choose_ne_zero_iff.mp hcparts.2
            omega
          simp [hc0]
        simp [hpgf0, hchoose0]

/-- Exponential tilting of the lower tail.  This is the elementary first
step in Chvátal's finite proof: on `j ≤ t` and `0 < q ≤ 1`, `q^t ≤ q^j`.
No probabilistic or asymptotic assumption is used. -/
theorem pow_mul_hypergeomLowerCount_le
    (n m s t : Nat) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q ^ t * hypergeomLowerCount n m s t ≤
      ∑ j ∈ Finset.range (t + 1),
        q ^ j * hypergeomCount n m s j := by
  rw [hypergeomLowerCount, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjt : j ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hp : q ^ t ≤ q ^ j := by
    exact pow_le_pow_of_le_one hq0 hq1 hjt
  exact mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)

/-- Floor-free exponential tilting, matching the real cutoff and exponent in
CS87 exactly. -/
theorem rpow_mul_hypergeomLowerCountReal_le
    (n m s : Nat) {r q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    q ^ r * hypergeomLowerCountReal n m s r ≤
      ∑ j ∈ (Finset.range (s + 1)).filter fun j : Nat => (j : ℝ) ≤ r,
        q ^ (j : ℝ) * hypergeomCount n m s j := by
  rw [hypergeomLowerCountReal, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjr : (j : ℝ) ≤ r := (Finset.mem_filter.mp hj).2
  have hp : q ^ r ≤ q ^ (j : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hjr
  exact mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)

/-- The exact analytic constant conversion in CS87 (6.4).  Once the finite
weighted coefficient bound gives the middle expression, the hypotheses
`m / n ≥ 2r / s` turn it into `(2 / e)^r`. -/
theorem two_rpow_mul_one_sub_half_density_pow_le
    {n m s : Nat} {r : ℝ} (hn : 0 < n) (hmn : m ≤ n)
    (hmean : 2 * (n : ℝ) * r ≤ (m : ℝ) * s) :
    (2 : ℝ) ^ r * (1 - (m : ℝ) / (2 * n)) ^ s ≤
      (2 / Real.exp 1) ^ r := by
  let p : ℝ := (m : ℝ) / (2 * n)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 ≤ p := by
    dsimp [p]
    positivity
  have hp_half : p ≤ 1 / 2 := by
    dsimp [p]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)]
    have hmnr : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hbase0 : 0 ≤ 1 - p := by linarith
  have hone_exp : 1 - p ≤ Real.exp (-p) := by
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-p)
  have hpow : (1 - p) ^ s ≤ (Real.exp (-p)) ^ s := by
    exact pow_le_pow_left₀ hbase0 hone_exp s
  have hrmean : r ≤ p * s := by
    dsimp [p]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmean
  calc
    (2 : ℝ) ^ r * (1 - (m : ℝ) / (2 * n)) ^ s =
        (2 : ℝ) ^ r * (1 - p) ^ s := by rfl
    _ ≤ (2 : ℝ) ^ r * (Real.exp (-p)) ^ s :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2 : ℝ) ^ r * Real.exp (-(p * s)) := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ (2 : ℝ) ^ r * Real.exp (-r) := by
      gcongr
    _ = (2 / Real.exp 1) ^ r := by
      rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 2)]
      rw [Real.rpow_def_of_pos (by positivity :
        (0 : ℝ) < 2 / Real.exp 1)]
      rw [← Real.exp_add]
      congr 1
      rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0)
        (Real.exp_ne_zero 1), Real.log_exp]
      ring

/-- CS87 equation (6.4), with the real cutoff encoding the floor exactly. -/
theorem hypergeomLowerCountReal_le_cs87
    {n m s : Nat} {r : ℝ} (hn : 0 < n) (hmn : m ≤ n)
    (hmean : 2 * (n : ℝ) * r ≤ (m : ℝ) * s) :
    (hypergeomLowerCountReal n m s r : ℝ) ≤
      (n.choose s : ℝ) * (2 / Real.exp 1) ^ r := by
  have htilt := rpow_mul_hypergeomLowerCountReal_le
    n m s (r := r) (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hfilter :
      (∑ j ∈ (Finset.range (s + 1)).filter
          (fun j : Nat => (j : ℝ) ≤ r),
          (1 / 2 : ℝ) ^ (j : ℝ) * hypergeomCount n m s j) ≤
        hypergeomPGF n m s (1 / 2 : ℝ) := by
    dsimp [hypergeomPGF]
    simpa only [Real.rpow_natCast] using
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun j hj₁ hj₂ => by positivity)
  have hw := weighted_vandermonde_le n m s hn hmn
    (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hw' :
      hypergeomPGF n m s (1 / 2 : ℝ) ≤
        (n.choose s : ℝ) * (1 - (m : ℝ) / (2 * n)) ^ s := by
    convert hw using 1 <;> ring
  have hanalytic := two_rpow_mul_one_sub_half_density_pow_le
    (n := n) (m := m) (s := s) (r := r) hn hmn hmean
  have hinv : (2 : ℝ) ^ r * (1 / 2 : ℝ) ^ r = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    norm_num
  calc
    (hypergeomLowerCountReal n m s r : ℝ) =
        (2 : ℝ) ^ r * ((1 / 2 : ℝ) ^ r *
          hypergeomLowerCountReal n m s r) := by
      rw [← mul_assoc, hinv, one_mul]
    _ ≤ (2 : ℝ) ^ r *
        ∑ j ∈ (Finset.range (s + 1)).filter
          (fun j : Nat => (j : ℝ) ≤ r),
          (1 / 2 : ℝ) ^ (j : ℝ) * hypergeomCount n m s j := by
      exact mul_le_mul_of_nonneg_left htilt (by positivity)
    _ ≤ (2 : ℝ) ^ r * hypergeomPGF n m s (1 / 2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hfilter (by positivity)
    _ ≤ (2 : ℝ) ^ r *
        ((n.choose s : ℝ) * (1 - (m : ℝ) / (2 * n)) ^ s) := by
      exact mul_le_mul_of_nonneg_left hw' (by positivity)
    _ = (n.choose s : ℝ) *
        ((2 : ℝ) ^ r * (1 - (m : ℝ) / (2 * n)) ^ s) := by ring
    _ ≤ (n.choose s : ℝ) * (2 / Real.exp 1) ^ r := by
      exact mul_le_mul_of_nonneg_left hanalytic (Nat.cast_nonneg _)

end AvgCaseMls.Section3
