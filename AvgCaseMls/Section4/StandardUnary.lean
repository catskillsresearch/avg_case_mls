import AvgCaseMls.Example41
import AvgCaseMls.Section4.RankFamily

/-!
# The standard inverse-square unary distribution

The string `0^m` represents the positive integer `m + 1`.  Its probability is
exactly `6 / (π² (m + 1)²)`.  This shifted convention gives the positive
integers a total encoding (including `1`) while retaining the executable unary
rank program from `RankFamily`.
-/

namespace AvgCaseMls.Section4

open AvgCaseMls.Foundation

namespace StandardUnary

noncomputable def weight (m : Nat) : NNReal :=
  Real.toNNReal ((6 / Real.pi ^ 2) * ((m + 1 : Nat) : ℝ) ^ (-2 : ℝ))

theorem weight_pos (m : Nat) : 0 < weight m := by
  rw [weight, Real.toNNReal_pos]
  positivity

theorem weight_strictAnti : StrictAnti weight := by
  intro m n hmn
  rw [weight, weight, Real.toNNReal_lt_toNNReal_iff (by positivity)]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  apply Real.rpow_lt_rpow_of_neg (by positivity)
    (by exact_mod_cast Nat.succ_lt_succ hmn)
    (by norm_num)

@[simp] theorem coe_weight (m : Nat) :
    (weight m : ℝ) =
      (6 / Real.pi ^ 2) * ((m + 1 : Nat) : ℝ) ^ (-2 : ℝ) := by
  rw [weight, Real.coe_toNNReal]
  positivity

theorem weight_summable : Summable weight := by
  rw [← NNReal.summable_coe]
  have h :
      Summable (fun m : Nat =>
        (6 / Real.pi ^ 2) * ((m + 1 : Nat) : ℝ) ^ (-2 : ℝ)) := by
    exact ((summable_nat_add_iff 1).2
      ((Real.summable_nat_rpow).2 (by norm_num))).mul_left
        (6 / Real.pi ^ 2)
  simpa only [coe_weight] using h

theorem tsum_weight : ∑' m, weight m = 1 := by
  apply NNReal.eq
  rw [NNReal.coe_tsum]
  simp_rw [coe_weight]
  calc
    (∑' m : Nat,
        (6 / Real.pi ^ 2) * ((m + 1 : Nat) : ℝ) ^ (-2 : ℝ)) =
        (6 / Real.pi ^ 2) *
          ∑' m : Nat, ((m + 1 : Nat) : ℝ) ^ (-2 : ℝ) := by
            rw [tsum_mul_left]
    _ = (6 / Real.pi ^ 2) *
          ∑' n : Nat, (n : ℝ) ^ (-2 : ℝ) := by
            congr 1
            let f : Nat → ℝ := fun n => (n : ℝ) ^ (-2 : ℝ)
            have hf : Summable f :=
              (Real.summable_nat_rpow).2 (by norm_num)
            have hs : HasSum (fun n => f (n + 1)) (∑' n, f n) := by
              apply (hasSum_nat_add_iff 1).2
              simpa [f] using hf.hasSum
            simpa [f] using hs.tsum_eq
    _ = 1 := by
      rw [Example41.tsum_nat_rpow_neg_two]
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp

noncomputable def prob (x : Bitstring) : NNReal :=
  if UnaryRank.OnSupport x then weight x.length else 0

@[simp] theorem prob_code (m : Nat) :
    prob (UnaryRank.code m) = weight m := by
  simp [prob, UnaryRank.OnSupport, UnaryRank.code]

theorem prob_eq_zero_of_not_support {x : Bitstring}
    (hx : ¬ UnaryRank.OnSupport x) : prob x = 0 := by
  simp [prob, hx]

theorem support_subset_range :
    Function.support prob ⊆ Set.range UnaryRank.code := by
  intro x hx
  by_contra h
  apply hx
  apply prob_eq_zero_of_not_support
  exact fun hs => h ⟨x.length, hs.symm⟩

theorem summable_prob : Summable prob := by
  apply (UnaryRank.code_injective.summable_iff
    (f := prob) (fun x hx => prob_eq_zero_of_not_support (by
      intro hs
      exact hx ⟨x.length, hs.symm⟩))).mp
  have heq : prob ∘ UnaryRank.code = weight := by
    funext n
    exact prob_code n
  rw [heq]
  exact weight_summable

theorem tsum_prob : ∑' x, prob x = 1 := by
  symm
  calc
    1 = ∑' n, prob (UnaryRank.code n) := by
      simpa only [prob_code] using tsum_weight.symm
    _ = ∑' x, prob x :=
      UnaryRank.code_injective.tsum_eq support_subset_range

theorem superlevel_code (n : Nat) :
    {x : Bitstring | prob (UnaryRank.code n) ≤ prob x} =
      UnaryRank.code '' Set.Iic n := by
  ext x
  constructor
  · intro hx
    change prob (UnaryRank.code n) ≤ prob x at hx
    have hxp : prob x ≠ 0 := by
      intro hz
      rw [hz, prob_code] at hx
      exact (not_le_of_gt (weight_pos n)) hx
    have hs : UnaryRank.OnSupport x := by
      by_contra h
      exact hxp (prob_eq_zero_of_not_support h)
    refine ⟨x.length, ?_, hs.symm⟩
    change x.length ≤ n
    by_contra hlen
    have := weight_strictAnti (Nat.lt_of_not_ge hlen)
    rw [prob_code, show prob x = weight x.length by simp [prob, hs]] at hx
    exact (not_le_of_gt this) hx
  · rintro ⟨m, hm, rfl⟩
    change prob (UnaryRank.code n) ≤ prob (UnaryRank.code m)
    simpa only [prob_code] using
      (weight_strictAnti.antitone hm)

noncomputable def distribution : Subprobability where
  prob := prob
  summable_prob := summable_prob
  tsum_le_one := by rw [tsum_prob]
  finite_superlevel := by
    intro x hx
    have hs : UnaryRank.OnSupport x := by
      by_contra h
      exact hx (prob_eq_zero_of_not_support h)
    rw [show x = UnaryRank.code x.length from hs]
    rw [superlevel_code]
    exact (Set.finite_Iic x.length).image UnaryRank.code

@[simp] theorem distribution_prob_code (m : Nat) :
    distribution.prob (UnaryRank.code m) =
      Real.toNNReal
        ((6 / Real.pi ^ 2) * ((m + 1 : Nat) : ℝ) ^ (-2 : ℝ)) := by
  exact prob_code m

@[simp] theorem distribution_rank_code (m : Nat) :
    distribution.rank (UnaryRank.code m) = m + 1 := by
  rw [Subprobability.rank_eq_ncard_of_prob_ne_zero _ _
    (by rw [distribution_prob_code]
        exact ne_of_gt (weight_pos m))]
  change Set.ncard
    {x : Bitstring | prob (UnaryRank.code m) ≤ prob x} = m + 1
  rw [superlevel_code, Set.ncard_image_of_injective _
    UnaryRank.code_injective]
  exact Set.ncard_Iic_nat m

theorem distribution_rank_eq (x : Bitstring) :
    distribution.rank x =
      if UnaryRank.OnSupport x then x.length + 1 else 0 := by
  split_ifs with hx
  · rw [hx]
    simpa [UnaryRank.code] using distribution_rank_code x.length
  · apply Subprobability.rank_eq_zero_of_prob_eq_zero
    exact prob_eq_zero_of_not_support hx

theorem rank_eq_geometric :
    distribution.rank = (UnaryRank.distribution 0).rank := by
  funext x
  rw [distribution_rank_eq, UnaryRank.distribution_rank_eq]

theorem rankable : IsPolynomialTimeRankable distribution := by
  obtain ⟨program, time, hpoly, hmono, hcompute⟩ :=
    UnaryRank.distribution_rankable 0
  refine ⟨program, time, hpoly, hmono, ?_⟩
  intro x
  simpa only [rank_eq_geometric] using hcompute x

theorem mass_eq_one : distribution.mass = 1 :=
  tsum_prob

private noncomputable def rankTerm {L : Set Bitstring} (d : Decider L) (T : TimeScale)
    (l : Nat) (x : Bitstring) : NNReal :=
  if distribution.prob x ≠ 0 ∧ distribution.rank x ≤ l
  then (T.inverse (d.actualRuntime x) : NNReal) / (max 1 x.length : Nat)
  else 0

private theorem rankTerm_finite_support {L : Set Bitstring}
    (d : Decider L) (T : TimeScale) (l : Nat) :
    Set.Finite (Function.support (rankTerm d T l)) := by
  apply Set.Finite.subset
    ((Set.finite_Iic l).image UnaryRank.code)
  intro x hx
  simp only [Function.mem_support, ne_eq, rankTerm] at hx
  by_cases hprob : distribution.prob x = 0
  · simp [hprob] at hx
  have hs : UnaryRank.OnSupport x := by
    by_contra h
    exact hprob (prob_eq_zero_of_not_support h)
  have hrank : distribution.rank x = x.length + 1 := by
    rw [distribution_rank_eq, if_pos hs]
  have hle : x.length + 1 ≤ l := by
    by_contra h
    have hxpair :
        x.length < l ∧ T.inverse (d.actualRuntime x) ≠ 0 := by
      simpa [hprob, hrank] using hx
    have hx' : x.length < l := by
      exact hxpair.1
    exact h (by omega)
  refine ⟨x.length, ?_, hs.symm⟩
  exact Set.mem_Iic.mpr (by omega)

private theorem rankTerm_summable {L : Set Bitstring}
    (d : Decider L) (T : TimeScale) (l : Nat) :
    Summable (rankTerm d T l) :=
  summable_of_hasFiniteSupport (rankTerm_finite_support d T l)

/--
The pointwise step in the paper's `n³` calculation.  For the unary atom
representing `m + 1`, the rank-average inequality bounds the inverse runtime
by `(m + 1) * max 1 m`, and hence by `(m + 1)³`.
-/
theorem inverse_runtime_le_cubic {L : Set Bitstring}
    (d : Decider L) (T : TimeScale)
    (havg : IsAverageTime d distribution T) (m : Nat) :
    T.inverse (d.actualRuntime (UnaryRank.code m)) ≤ (m + 1) ^ 3 := by
  let x := UnaryRank.code m
  let l := m + 1
  let term : Bitstring → NNReal := rankTerm d T l
  have hterm :
      term x =
        (T.inverse (d.actualRuntime x) : NNReal) / (max 1 x.length : Nat) := by
    rw [show term x = rankTerm d T l x by rfl, rankTerm, if_pos]
    constructor
    · change distribution.prob (UnaryRank.code m) ≠ 0
      rw [distribution_prob_code]
      exact ne_of_gt (weight_pos m)
    · change distribution.rank (UnaryRank.code m) ≤ m + 1
      simp
  have hcost :
      rankCost d distribution T l = ∑' y, term y := by
    rfl
  have hsingle : term x ≤ rankCost d distribution T l := by
    rw [hcost]
    exact (rankTerm_summable d T l).le_tsum x (fun _ _ => zero_le)
  have havg' : rankCost d distribution T l ≤ l := havg l (by omega)
  have hquot :
      (T.inverse (d.actualRuntime x) : NNReal) /
          (max 1 x.length : Nat) ≤ l := by
    rw [← hterm]
    exact hsingle.trans havg'
  have hinv :
      T.inverse (d.actualRuntime x) ≤ l * max 1 x.length := by
    exact_mod_cast (div_le_iff₀
      (show (0 : NNReal) < (max 1 x.length : Nat) by positivity)).mp hquot
  change T.inverse (d.actualRuntime (UnaryRank.code m)) ≤ (m + 1) ^ 3
  have hcubic : (m + 1) * max 1 m ≤ (m + 1) ^ 3 := by
    calc
      (m + 1) * max 1 m ≤ (m + 1) * (m + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      _ ≤ (m + 1) ^ 3 := by
        rw [show (m + 1) * (m + 1) = (m + 1) ^ 2 by ring,
          show (m + 1) ^ 3 = (m + 1) ^ 2 * (m + 1) by ring]
        exact Nat.le_mul_of_pos_right _ (by omega)
  have hinv' :
      T.inverse (d.actualRuntime (UnaryRank.code m)) ≤
        (m + 1) * max 1 m := by
    simpa [x, l, UnaryRank.code] using hinv
  exact hinv'.trans hcubic

theorem runtime_le_scale_cubic {L : Set Bitstring}
    (d : Decider L) (T : TimeScale)
    (havg : IsAverageTime d distribution T) (m : Nat) :
    d.actualRuntime (UnaryRank.code m) ≤ T ((m + 1) ^ 3) := by
  exact (T.inverse_spec _).trans
    (T.monotone (inverse_runtime_le_cubic d T havg m))

end StandardUnary

end AvgCaseMls.Section4
