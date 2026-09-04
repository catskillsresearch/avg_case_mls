import AvgCaseMls.Foundation
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Interval.Set.Nat

/-!
# Infinite-support distributions with a linear-time rank

The support consists of the unary-zero strings `0^n`.  Every member has rank
`n + 1`; malformed strings have probability and rank zero.  Varying the
parameter of a geometric law gives infinitely many distinct probability
distributions without changing this rank.
-/

namespace AvgCaseMls.Section4

open AvgCaseMls.Foundation

namespace UnaryRank

def code (n : Nat) : Bitstring := List.replicate n false

theorem code_injective : Function.Injective code := by
  intro m n h
  have := congrArg List.length h
  simpa [code] using this

def OnSupport (x : Bitstring) : Prop := x = code x.length

instance (x : Bitstring) : Decidable (OnSupport x) := by
  unfold OnSupport
  infer_instance

noncomputable def weight (k n : Nat) : NNReal :=
  Real.toNNReal (((1 / 2 : ℝ) ^ n) / (2 * (k + 1)))

theorem weight_hasSum (k : Nat) :
    HasSum (weight k) (Real.toNNReal (1 / (k + 1 : ℝ))) := by
  have hgeom :
      HasSum (fun n : Nat => ((1 / 2 : ℝ) ^ n) / (2 * (k + 1))) (1 / (k + 1)) := by
    have h := hasSum_geometric_two.div_const (2 * (k + 1 : ℝ))
    have heq : (2 : ℝ) / (2 * (k + 1)) = 1 / (k + 1) := by
      field_simp
    rw [heq] at h
    exact h
  exact hgeom.toNNReal (fun n => by positivity)

theorem weight_summable (k : Nat) : Summable (weight k) :=
  (weight_hasSum k).summable

theorem weight_pos (k n : Nat) : 0 < weight k n := by
  simp [weight]
  positivity

theorem weight_strictAnti (k : Nat) : StrictAnti (weight k) := by
  intro m n hmn
  rw [weight, weight, Real.toNNReal_lt_toNNReal_iff (by positivity)]
  apply div_lt_div_of_pos_right _ (by positivity)
  simpa [one_div, inv_pow] using
    (one_div_pow_strictAnti (by norm_num : (1 : ℝ) < 2) hmn)

noncomputable def prob (k : Nat) (x : Bitstring) : NNReal :=
  if OnSupport x then weight k x.length else 0

@[simp] theorem prob_code (k n : Nat) : prob k (code n) = weight k n := by
  simp [prob, OnSupport, code]

theorem prob_eq_zero_of_not_support (k : Nat) {x : Bitstring}
    (hx : ¬ OnSupport x) : prob k x = 0 := by
  simp [prob, hx]

theorem support_subset_range (k : Nat) :
    Function.support (prob k) ⊆ Set.range code := by
  intro x hx
  by_contra h
  apply hx
  apply prob_eq_zero_of_not_support
  exact fun hs => h ⟨x.length, hs.symm⟩

theorem summable_prob (k : Nat) : Summable (prob k) := by
  apply (code_injective.summable_iff
    (f := prob k) (fun x hx => prob_eq_zero_of_not_support k (by
      intro hs
      exact hx ⟨x.length, hs.symm⟩))).mp
  have heq : prob k ∘ code = weight k := by
    funext n
    exact prob_code k n
  rw [heq]
  exact weight_summable k

theorem tsum_prob (k : Nat) :
    ∑' x, prob k x = Real.toNNReal (1 / (k + 1 : ℝ)) := by
  symm
  calc
    Real.toNNReal (1 / (k + 1 : ℝ)) = ∑' n, prob k (code n) := by
      simpa only [prob_code] using (weight_hasSum k).tsum_eq.symm
    _ = ∑' x, prob k x :=
      code_injective.tsum_eq (support_subset_range k)

theorem superlevel_code (k n : Nat) :
    {x : Bitstring | prob k (code n) ≤ prob k x} =
      code '' Set.Iic n := by
  ext x
  constructor
  · intro hx
    change prob k (code n) ≤ prob k x at hx
    have hxp : prob k x ≠ 0 := by
      intro hz
      rw [hz, prob_code] at hx
      exact (not_le_of_gt (weight_pos k n)) hx
    have hs : OnSupport x := by
      by_contra h
      exact hxp (prob_eq_zero_of_not_support k h)
    refine ⟨x.length, ?_, hs.symm⟩
    change x.length ≤ n
    by_contra hlen
    have hlt : n < x.length := Nat.lt_of_not_ge hlen
    have := weight_strictAnti k hlt
    rw [prob_code, prob, if_pos hs] at hx
    exact (not_le_of_gt this) hx
  · rintro ⟨m, hm, rfl⟩
    have hweight : weight k n ≤ weight k m := by
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · exact le_rfl
      · exact (weight_strictAnti k hlt).le
    exact show prob k (code n) ≤ prob k (code m) by
      simpa only [prob_code] using hweight

noncomputable def distribution (k : Nat) : Subprobability where
  prob := prob k
  summable_prob := summable_prob k
  tsum_le_one := by
    rw [tsum_prob]
    rw [Real.toNNReal_le_iff_le_coe]
    rw [div_eq_mul_inv, one_mul]
    exact (inv_le_one₀ (show (0 : ℝ) < (k : ℝ) + 1 by positivity)).2
      (by norm_num)
  finite_superlevel := by
    intro x hx
    have hs : OnSupport x := by
      by_contra h
      exact hx (prob_eq_zero_of_not_support k h)
    rw [show x = code x.length from hs]
    rw [superlevel_code]
    exact (Set.finite_Iic x.length).image code

@[simp] theorem distribution_prob_code (k n : Nat) :
    (distribution k).prob (code n) = weight k n := prob_code k n

@[simp] theorem distribution_rank_code (k n : Nat) :
    (distribution k).rank (code n) = n + 1 := by
  rw [Subprobability.rank_eq_ncard_of_prob_ne_zero _ _
    (by simpa using (ne_of_gt (weight_pos k n) : weight k n ≠ 0))]
  change Set.ncard {x : Bitstring | prob k (code n) ≤ prob k x} = n + 1
  rw [superlevel_code, Set.ncard_image_of_injective _ code_injective]
  exact Set.ncard_Iic_nat n

theorem distribution_rank_eq (k : Nat) (x : Bitstring) :
    (distribution k).rank x = if OnSupport x then x.length + 1 else 0 := by
  split_ifs with hx
  · rw [hx]
    simpa [code] using distribution_rank_code k x.length
  · apply Subprobability.rank_eq_zero_of_prob_eq_zero
    exact prob_eq_zero_of_not_support k hx

def supportTestMachine : Machine :=
  ⟨#[.branch 3 1 2, .moveRight 0, .halt false, .halt true]⟩

def scanConfig (left : List TapeSymbol) : Bitstring → Config
  | [] => ⟨0, left, none, []⟩
  | b :: bs => ⟨0, left, some b, bs.map some⟩

private theorem supportTestMachine_false_step (left : List TapeSymbol)
    (bs : Bitstring) (fuel elapsed : Nat) :
    evalFrom supportTestMachine (fuel + 2)
      (scanConfig left (false :: bs)) elapsed =
    evalFrom supportTestMachine fuel
      (scanConfig (some false :: left) bs) (elapsed + 2) := by
  cases bs <;>
    simp [scanConfig, evalFrom, step, supportTestMachine, moveRight]

private theorem supportTestMachine_go (left : List TapeSymbol)
    (xs : Bitstring) (elapsed : Nat) :
    ∃ r, evalFrom supportTestMachine (2 * xs.length + 2)
      (scanConfig left xs) elapsed = some r ∧
      (r.accept = true ↔ xs.all (· = false) = true) := by
  induction xs generalizing left elapsed with
  | nil =>
      refine ⟨⟨true, tapeOutput ⟨3, left, none, []⟩, elapsed + 2⟩, ?_, by simp⟩
      simp [scanConfig, evalFrom, step, supportTestMachine]
  | cons b bs ih =>
      cases b
      · obtain ⟨r, hr, ha⟩ := ih (some false :: left) (elapsed + 2)
        refine ⟨r, ?_, ?_⟩
        · rw [show 2 * (false :: bs).length + 2 =
              (2 * bs.length + 2) + 2 by simp; omega]
          rw [supportTestMachine_false_step]
          exact hr
        · simpa using ha
      · refine ⟨⟨false, tapeOutput ⟨2, left, some true, bs.map some⟩,
          elapsed + 2⟩, ?_, ?_⟩
        · norm_num [scanConfig, evalFrom, step, supportTestMachine]
        · simp [List.all_cons]

theorem onSupport_iff_all (x : Bitstring) :
    OnSupport x ↔ x.all (· = false) = true := by
  rw [OnSupport, code, List.eq_replicate_length]
  simp

theorem supportTestMachine_correct (x : Bitstring) :
    ∃ r, eval supportTestMachine (2 * x.length + 2) x = some r ∧
      (r.accept = true ↔ OnSupport x) := by
  obtain ⟨r, hr, ha⟩ := supportTestMachine_go [] x 0
  refine ⟨r, ?_, ?_⟩
  · change evalFrom supportTestMachine (2 * x.length + 2)
      (scanConfig [] x) 0 = some r
    exact hr
  · exact ha.trans (onSupport_iff_all x).symm

def rankMachine : Machine :=
  ⟨#[.branch 3 1 3, .write (some true) 2, .moveRight 0,
      .write (some true) 4, .halt true]⟩

private theorem rankMachine_false_step (left : List TapeSymbol)
    (n fuel elapsed : Nat) :
    evalFrom rankMachine (fuel + 3)
      (scanConfig left (code (n + 1))) elapsed =
    evalFrom rankMachine fuel
      (scanConfig (some true :: left) (code n)) (elapsed + 3) := by
  have hcode : code (n + 1) = false :: code n := by
    unfold code
    rw [show n + 1 = Nat.succ n by omega, List.replicate_succ]
  rw [hcode]
  cases h : code n <;>
    simp [scanConfig, evalFrom, step, rankMachine, moveRight]

private theorem rankMachine_go (left : List TapeSymbol) (n elapsed : Nat) :
    evalFrom rankMachine (3 * n + 3) (scanConfig left (code n)) elapsed =
      some ⟨true, left.reverse.filterMap id ++ List.replicate (n + 1) true,
        elapsed + (3 * n + 3)⟩ := by
  induction n generalizing left elapsed with
  | zero =>
      simp [code, scanConfig, evalFrom, step, rankMachine, tapeOutput]
  | succ n ih =>
      rw [show 3 * (n + 1) + 3 = (3 * n + 3) + 3 by omega]
      rw [rankMachine_false_step]
      rw [ih (some true :: left) (elapsed + 3)]
      congr 2
      · simp [List.filterMap_reverse,
          List.replicate_succ, List.append_assoc]
      · omega

theorem rankMachine_code (n : Nat) :
    eval rankMachine (3 * n + 3) (code n) =
      some ⟨true, List.replicate (n + 1) true, 3 * n + 3⟩ := by
  change evalFrom rankMachine (3 * n + 3) (scanConfig [] (code n)) 0 =
    some ⟨true, List.replicate (n + 1) true, 3 * n + 3⟩
  simpa using rankMachine_go [] n 0

def rankProgram : Program :=
  .branch (.machine supportTestMachine)
    (.compose (.machine rankMachine) .encodeLength)
    (.constant false (encodeNat 0))

def rankTime (n : Nat) : Nat := 3 * n + 3

theorem rankTime_polynomial : IsPolynomial rankTime :=
  .bounded 3 1 (fun n => by simp [rankTime])

theorem rankTime_monotone : Monotone rankTime := by
  intro a b h
  simp [rankTime]
  omega

-- Machine correctness is proved below from the evaluator equations.
theorem rankProgram_computes (k : Nat) :
    ComputesNatWithin rankProgram (distribution k).rank rankTime := by
  intro x
  by_cases hx : OnSupport x
  · have hxeq : x = code x.length := hx
    let conditionFuel := 2 * x.length + 2
    obtain ⟨conditionResult, hcondition, haccept⟩ :=
      supportTestMachine_correct x
    have hcondition' := AvgCaseMls.Foundation.eval_mono supportTestMachine
      (show conditionFuel ≤ rankTime (len x) by
        simp [conditionFuel, rankTime, len]
        omega) hcondition
    have hrank := rankMachine_code x.length
    have hrank' := AvgCaseMls.Foundation.eval_mono rankMachine
      (show 3 * x.length + 3 ≤ rankTime (len x) by
        simp [rankTime, len]) hrank
    have hrankx :
        eval rankMachine (rankTime (len x)) x =
          some ⟨true, List.replicate (x.length + 1) true,
            3 * x.length + 3⟩ := by
      rw [hxeq]
      simpa [code] using hrank'
    have haccept' : conditionResult.accept = true := haccept.mpr hx
    change eval supportTestMachine (rankTime (List.length x)) x =
      some conditionResult at hcondition'
    change eval rankMachine (rankTime (List.length x)) x =
      some ⟨true, List.replicate (x.length + 1) true,
        3 * x.length + 3⟩ at hrankx
    refine ⟨{
      accept := true
      output := encodeNat (x.length + 1)
      steps := conditionResult.steps + ((3 * x.length + 3) + (x.length + 2))
    }, ?_, ?_⟩
    · simp [rankProgram, Program.eval, hcondition', haccept', hrankx]
    · change encodeNat (x.length + 1) = encodeNat ((distribution k).rank x)
      rw [distribution_rank_eq, if_pos hx]
  · let conditionFuel := 2 * x.length + 2
    obtain ⟨conditionResult, hcondition, haccept⟩ :=
      supportTestMachine_correct x
    have hcondition' := AvgCaseMls.Foundation.eval_mono supportTestMachine
      (show conditionFuel ≤ rankTime (len x) by
        simp [conditionFuel, rankTime, len]
        omega) hcondition
    have haccept' : conditionResult.accept = false := by
      cases h : conditionResult.accept
      · rfl
      · exact False.elim (hx (haccept.mp h))
    refine ⟨⟨false, encodeNat 0, conditionResult.steps + 1⟩, ?_, ?_⟩
    · simp only [rankProgram, Program.eval]
      rw [hcondition']
      simp [haccept']
    · simp [distribution_rank_eq, hx]

theorem distribution_rankable (k : Nat) :
    IsPolynomialTimeRankable (distribution k) :=
  ⟨rankProgram, rankTime, rankTime_polynomial, rankTime_monotone,
    rankProgram_computes k⟩

theorem distribution_rank_independent (j k : Nat) :
    (distribution j).rank = (distribution k).rank := by
  funext x
  rw [distribution_rank_eq, distribution_rank_eq]

theorem distribution_ne_of_ne {j k : Nat} (h : j ≠ k) :
    distribution j ≠ distribution k := by
  intro heq
  have hp := congrArg (fun μ : Subprobability => μ.prob (code 0)) heq
  have hp' := congrArg (fun q : NNReal => (q : ℝ)) hp
  simp only [distribution_prob_code, weight,
    Real.coe_toNNReal _ (by positivity : 0 ≤ ((1 / 2 : ℝ) ^ 0) / (2 * (j + 1))),
    Real.coe_toNNReal _ (by positivity : 0 ≤ ((1 / 2 : ℝ) ^ 0) / (2 * (k + 1)))] at hp'
  norm_num at hp'
  apply h
  have hp'' : (2 * ((j : ℝ) + 1))⁻¹ = (2 * ((k : ℝ) + 1))⁻¹ := by
    simpa [div_eq_mul_inv, mul_assoc] using hp'
  have hden := inv_injective hp''
  exact_mod_cast (by
    nlinarith [hden] : (j : ℝ) = k)

theorem infinitely_many_distributions :
    Set.Infinite (Set.range distribution) :=
  Set.infinite_range_of_injective (fun _ _ h => by
    by_contra hne
    exact distribution_ne_of_ne hne h)

end UnaryRank

end AvgCaseMls.Section4
