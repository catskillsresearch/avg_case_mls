import AvgCaseMls.Section3.Hypergraph

/-!
# Analytic estimates for CS87 Lemma 1

This file records the constants and the two geometric tails used in the proof
of Chvátal--Szemerédi's local-sparsity lemma.
-/

namespace AvgCaseMls.Section3

open Filter

/-- Sampling without replacement is no more likely to stay in a fixed
`s`-set than `k` independent samples are. -/
theorem choose_ratio_le_pow_ratio {k s n : Nat} (hk : k ≤ s) (hs : s ≤ n)
    (hkpos : 0 < k) :
    ((s.choose k : Nat) : ℝ) / n.choose k ≤
      ((s : ℝ) / n) ^ k := by
  have hnpos : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le hkpos hk) hs
  have hnchoose : (0 : ℝ) < n.choose k := by
    exact_mod_cast Nat.choose_pos (hk.trans hs)
  rw [div_pow, div_le_div_iff₀ hnchoose (pow_pos (by exact_mod_cast hnpos) _)]
  norm_cast
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos k)
  calc
    k.factorial * (s.choose k * n ^ k) =
        s.descFactorial k * n ^ k := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      simp [mul_assoc]
    _ ≤ n.descFactorial k * s ^ k := by
      rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
      rw [show n ^ k = ∏ _i ∈ Finset.range k, n by simp,
        show s ^ k = ∏ _i ∈ Finset.range k, s by simp,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i hi => ?_)
      simp only [Finset.mem_range] at hi
      have his : i ≤ s := le_trans (Nat.le_of_lt hi) hk
      have hin : i ≤ n := his.trans hs
      have hs_eq : s - i + i = s := Nat.sub_add_cancel his
      have hn_eq : n - i + i = n := Nat.sub_add_cancel hin
      nlinarith [Nat.mul_le_mul_left i hs]
    _ = k.factorial * (s ^ k * n.choose k) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      simp [mul_assoc, mul_comm]

/-- The elementary factorial estimate `r^r ≤ e^r r!` used in the standard
upper bound for a binomial coefficient. -/
theorem self_pow_le_exp_pow_mul_factorial (r : Nat) :
    (r : ℝ) ^ r ≤ (Real.exp 1) ^ r * r.factorial := by
  induction r with
  | zero => norm_num
  | succ r ihr =>
      rcases r with _ | r
      · norm_num
      · let q : ℝ := (r + 1 : Nat)
        have hq : 0 < q := by positivity
        have hbinom :
            (q + 1) ^ (r + 1) ≤ q ^ (r + 1) * Real.exp 1 := by
          have h := Real.one_add_inv_pow_le_exp (n := r + 1)
          have hid : q + 1 = q * (1 + q⁻¹) := by
            field_simp [q]
          rw [hid, mul_pow]
          gcongr
        calc
          (((r + 1 + 1 : Nat) : ℝ) ^ (r + 1 + 1)) =
              (q + 1) * (q + 1) ^ (r + 1) := by
                simp only [Nat.cast_add, Nat.cast_one, q]
                ring
          _ ≤ (q + 1) * (q ^ (r + 1) * Real.exp 1) := by
                gcongr
          _ ≤ (q + 1) *
              ((Real.exp 1) ^ (r + 1) * (r + 1).factorial *
                Real.exp 1) := by
                gcongr
          _ = (Real.exp 1) ^ (r + 1 + 1) *
              (r + 1 + 1).factorial := by
                simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
                  Nat.cast_one, pow_succ]
                dsimp [q]
                push_cast
                ring

/-- The standard estimate `m.choose r ≤ (e*m/r)^r`. -/
theorem choose_le_exp_mul_div_pow (m r : Nat) :
    ((m.choose r : Nat) : ℝ) ≤
      (Real.exp 1 * (m : ℝ) / r) ^ r := by
  rcases r with _ | r
  · simp
  have hrpos : (0 : ℝ) < r + 1 := by positivity
  have hfacpos : (0 : ℝ) < (r + 1).factorial := by positivity
  refine (Nat.choose_le_pow_div (α := ℝ) (r + 1) m).trans ?_
  rw [div_pow]
  push_cast
  rw [div_le_div_iff₀ hfacpos (pow_pos hrpos _)]
  have hfac := self_pow_le_exp_pow_mul_factorial (r + 1)
  push_cast at hfac
  calc
    (m : ℝ) ^ (r + 1) * (↑r + 1) ^ (r + 1) ≤
        (m : ℝ) ^ (r + 1) *
          ((Real.exp 1) ^ (r + 1) * (r + 1).factorial) :=
      mul_le_mul_of_nonneg_left hfac (pow_nonneg (Nat.cast_nonneg m) _)
    _ = (Real.exp 1 * (m : ℝ)) ^ (r + 1) *
        (r + 1).factorial := by rw [mul_pow]; ring

/-- The one-witness form of the elementary binomial-tail estimate. -/
theorem choose_mul_pow_le_tail_rpow {m r : Nat} {p t : ℝ}
    (hp : 0 < p) (ht : 0 < t) (htr : t < r)
    (hbase : Real.exp 1 * (m : ℝ) * p / t ≤ 1) :
    (m.choose r : ℝ) * p ^ r ≤
      (Real.exp 1 * (m : ℝ) * p / t) ^ t := by
  rcases m with _ | m
  · have hrpos : 0 < r := by exact_mod_cast (lt_trans ht htr)
    simp only [Nat.choose_eq_zero_of_lt hrpos, Nat.cast_zero, zero_mul]
    exact Real.rpow_nonneg (by norm_num) _
  let A := Real.exp 1 * ((m + 1 : Nat) : ℝ) * p / t
  let q := Real.exp 1 * ((m + 1 : Nat) : ℝ) / (r : ℝ) * p
  have hr : (0 : ℝ) < r := lt_trans ht htr
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hqA : q ≤ A := by
    dsimp [q, A]
    rw [div_mul_eq_mul_div]
    push_cast
    exact div_le_div_of_nonneg_left (by positivity) ht (le_of_lt htr)
  calc
    ((m + 1).choose r : ℝ) * p ^ r ≤
        (Real.exp 1 * ((m + 1 : Nat) : ℝ) / r) ^ r * p ^ r := by
          gcongr
          exact choose_le_exp_mul_div_pow (m + 1) r
    _ = q ^ r := by rw [← mul_pow]
    _ ≤ A ^ r := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast]
          exact Real.rpow_le_rpow hqpos.le hqA (Nat.cast_nonneg r)
    _ ≤ A ^ t := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_ge hApos
            (by simpa [A] using hbase) (le_of_lt htr)

/-- Any finite sub-sum of a geometric tail is bounded by the full tail. -/
theorem finset_sum_geometric_tail_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (a : Nat) (S : Finset Nat) (ha : ∀ s ∈ S, a ≤ s) :
    ∑ s ∈ S, q ^ s ≤ q ^ a / (1 - q) := by
  classical
  have hinj : Set.InjOn (fun s : Nat => s - a) S := by
    intro u hu v hv huv
    have hua := ha u hu
    have hva := ha v hv
    calc
      u = (u - a) + a := (Nat.sub_add_cancel hua).symm
      _ = (v - a) + a := by
        exact congrArg (fun z => z + a) huv
      _ = v := Nat.sub_add_cancel hva
  calc
    ∑ s ∈ S, q ^ s =
        ∑ s ∈ S, q ^ ((s - a) + a) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Nat.sub_add_cancel (ha s hs)]
    _ = ∑ j ∈ S.image (fun s : Nat => s - a), q ^ (j + a) := by
          rw [Finset.sum_image hinj]
    _ ≤ ∑' j : Nat, q ^ (j + a) := by
          apply Summable.sum_le_tsum
          · intro i hi
            positivity
          · simpa [pow_add] using
              (summable_geometric_of_norm_lt_one
                (show ‖q‖ < 1 by simpa [abs_of_nonneg hq0] using hq1)).mul_right
                (q ^ a)
    _ = (∑' j : Nat, q ^ j) * q ^ a := by
          simp_rw [pow_add]
          rw [tsum_mul_right]
    _ = q ^ a / (1 - q) := by
          rw [tsum_geometric_of_lt_one hq0 hq1]
          simp only [div_eq_mul_inv]
          ring

/-- CS87's `ε = y - 1/(k-1)`. -/
noncomputable def cs87Epsilon (k : Nat) (y : ℝ) : ℝ :=
  y - ((k - 1 : Nat) : ℝ)⁻¹

/-- The exponent `(k-1)ε = (k-1)y-1`. -/
noncomputable def cs87Alpha (k : Nat) (y : ℝ) : ℝ :=
  ((k - 1 : Nat) : ℝ) * cs87Epsilon k y

/-- The exact value of `x` chosen in CS87, Lemma 1. -/
noncomputable def cs87LocalSparsityX (c k : Nat) (y : ℝ) : ℝ :=
  ((1 / (2 * Real.exp 1)) *
      (y / ((c : ℝ) * Real.exp 1)) ^ y) ^
    (cs87Alpha k y)⁻¹

/-- The small-set geometric ratio `f(n)` from CS87. -/
noncomputable def cs87SmallRatio (c k : Nat) (y : ℝ) (n : Nat) : ℝ :=
  Real.exp 1 * (((c : ℝ) * Real.exp 1) / y) ^ y *
    (n : ℝ) ^ (-(cs87Alpha k y) / 2)

/-- The one-set estimate after multiplying by `n.choose s`. -/
noncomputable def cs87Envelope (c k : Nat) (y z : ℝ) : ℝ :=
  Real.exp 1 * (((c : ℝ) * Real.exp 1) / y) ^ y *
    z ^ (cs87Alpha k y)

/-- The sum of the two tails in equations (3.1) and (3.2). -/
noncomputable def cs87SplitMajorant (c k : Nat) (y : ℝ) (n : Nat) : ℝ :=
  (cs87SmallRatio c k y n) ^ k /
      (1 - cs87SmallRatio c k y n) +
    2 * (1 / 2 : ℝ) ^ n.sqrt

noncomputable def cs87SummationIndices (n k : Nat) (x : ℝ) : Finset Nat :=
  (Finset.range (n + 1)).filter fun s =>
    k ≤ s ∧ (s : ℝ) ≤ x * n

noncomputable def cs87EnvelopeSum
    (c k : Nat) (y x : ℝ) (n : Nat) : ℝ :=
  ∑ s ∈ cs87SummationIndices n k x,
    (cs87Envelope c k y ((s : ℝ) / n)) ^ s

theorem cs87_alpha_eq (hk : 1 < k) (y : ℝ) :
    cs87Alpha k y = ((k - 1 : Nat) : ℝ) * y - 1 := by
  simp only [cs87Alpha, cs87Epsilon]
  have hpos : (0 : ℝ) < (k - 1 : Nat) := by exact_mod_cast (Nat.sub_pos_of_lt hk)
  field_simp

theorem cs87_alpha_pos (hk : 1 < k) {y : ℝ}
    (hy : 1 < ((k - 1 : Nat) : ℝ) * y) :
    0 < cs87Alpha k y := by
  rw [cs87_alpha_eq hk]
  linarith

theorem cs87_localSparsityX_pos {c k : Nat} {y : ℝ}
    (hc : 0 < c) (hk : 1 < k) (hy : 1 < ((k - 1 : Nat) : ℝ) * y) :
    0 < cs87LocalSparsityX c k y := by
  have hypos : 0 < y := by
    have hkpos : (0 : ℝ) < (k - 1 : Nat) := by
      exact_mod_cast (Nat.sub_pos_of_lt hk)
    nlinarith
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have hbase :
      0 < (1 / (2 * Real.exp 1)) *
        (y / ((c : ℝ) * Real.exp 1)) ^ y := by
    positivity
  exact Real.rpow_pos_of_pos hbase _

theorem cs87_envelope_at_x {c k : Nat} {y : ℝ}
    (hc : 0 < c) (hk : 1 < k) (hy : 1 < ((k - 1 : Nat) : ℝ) * y) :
    cs87Envelope c k y (cs87LocalSparsityX c k y) = 1 / 2 := by
  have hypos : 0 < y := by
    have hkpos : (0 : ℝ) < (k - 1 : Nat) := by
      exact_mod_cast (Nat.sub_pos_of_lt hk)
    nlinarith
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have halpha : 0 < cs87Alpha k y := cs87_alpha_pos hk hy
  have hbase :
      0 ≤ (1 / (2 * Real.exp 1)) *
        (y / ((c : ℝ) * Real.exp 1)) ^ y := by positivity
  rw [cs87Envelope, cs87LocalSparsityX, ← Real.rpow_mul hbase]
  rw [inv_mul_cancel₀ halpha.ne', Real.rpow_one]
  have hprod :
      ((((c : ℝ) * Real.exp 1) / y) ^ y) *
          ((y / ((c : ℝ) * Real.exp 1)) ^ y) = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    field_simp
    simp
  calc
    Real.exp 1 * (((c : ℝ) * Real.exp 1) / y) ^ y *
        (1 / (2 * Real.exp 1) *
          (y / ((c : ℝ) * Real.exp 1)) ^ y) =
        (1 / 2) *
          ((((c : ℝ) * Real.exp 1) / y) ^ y *
            (y / ((c : ℝ) * Real.exp 1)) ^ y) := by
              field_simp
    _ = 1 / 2 := by rw [hprod]; ring

theorem cs87_envelope_le_half {c k : Nat} {y z : ℝ}
    (hc : 0 < c) (hk : 1 < k) (hy : 1 < ((k - 1 : Nat) : ℝ) * y)
    (hz : 0 ≤ z) (hzx : z ≤ cs87LocalSparsityX c k y) :
    cs87Envelope c k y z ≤ 1 / 2 := by
  have hypos : 0 < y := by
    have hkpos : (0 : ℝ) < (k - 1 : Nat) := by
      exact_mod_cast (Nat.sub_pos_of_lt hk)
    nlinarith
  have halpha : 0 ≤ cs87Alpha k y := (cs87_alpha_pos hk hy).le
  have hpow := Real.rpow_le_rpow hz hzx halpha
  unfold cs87Envelope
  calc
    Real.exp 1 * (((c : ℝ) * Real.exp 1) / y) ^ y *
        z ^ cs87Alpha k y ≤
      Real.exp 1 * (((c : ℝ) * Real.exp 1) / y) ^ y *
        (cs87LocalSparsityX c k y) ^ cs87Alpha k y := by
          gcongr
    _ = 1 / 2 := cs87_envelope_at_x hc hk hy

theorem cs87_envelope_le_smallRatio {c k n s : Nat} {y : ℝ}
    (hk : 1 < k) (hy : 1 < ((k - 1 : Nat) : ℝ) * y)
    (hn : 0 < n) (hs : (s : ℝ) ≤ Real.sqrt n) :
    cs87Envelope c k y ((s : ℝ) / n) ≤ cs87SmallRatio c k y n := by
  have hypos : 0 < y := by
    have hkpos : (0 : ℝ) < (k - 1 : Nat) := by
      exact_mod_cast (Nat.sub_pos_of_lt hk)
    nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hbase : (s : ℝ) / n ≤ ((n : ℝ) ^ (-(1 : ℝ) / 2)) := by
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hnR.le, ← Real.sqrt_eq_rpow]
    rw [div_le_iff₀ hnR, inv_mul_eq_div, le_div_iff₀ hsqrt]
    nlinarith [mul_le_mul_of_nonneg_right hs hsqrt.le,
      Real.sq_sqrt hnR.le]
  have halpha : 0 ≤ cs87Alpha k y := (cs87_alpha_pos hk hy).le
  have hz : 0 ≤ (s : ℝ) / n := by positivity
  have hpow := Real.rpow_le_rpow hz hbase halpha
  unfold cs87Envelope cs87SmallRatio
  calc
    Real.exp 1 * (((c : ℝ) * Real.exp 1) / y) ^ y *
        ((s : ℝ) / n) ^ cs87Alpha k y ≤
      Real.exp 1 * (((c : ℝ) * Real.exp 1) / y) ^ y *
        ((n : ℝ) ^ (-(1 : ℝ) / 2)) ^ cs87Alpha k y := by
          gcongr
    _ = Real.exp 1 * (((c : ℝ) * Real.exp 1) / y) ^ y *
        (n : ℝ) ^ (-cs87Alpha k y / 2) := by
          rw [← Real.rpow_mul hnR.le]
          congr 2
          ring

/-- After regrouping vertex sets by their cardinality, the normalized
witness coefficient is bounded by CS87's one-set envelope. -/
theorem cs87_aggregate_coefficient_le_envelope
    {c k n s R : Nat} {y : ℝ}
    (hc : 0 < c) (hk : 1 < k) (hy : 1 < ((k - 1 : Nat) : ℝ) * y)
    (hks : k ≤ s) (hsn : s ≤ n)
    (hsx : (s : ℝ) ≤ cs87LocalSparsityX c k y * n)
    (hR : y * (s : ℝ) < R) :
    (n.choose s : ℝ) * (c * n).choose R *
        (((s.choose k : Nat) : ℝ) / n.choose k) ^ R ≤
      (cs87Envelope c k y ((s : ℝ) / n)) ^ s := by
  have hkpos : 0 < k := lt_trans Nat.zero_lt_one hk
  have hspos : 0 < s := lt_of_lt_of_le hkpos hks
  have hnpos : 0 < n := hspos.trans_le hsn
  have hypos : 0 < y := by
    have hkm1 : (0 : ℝ) < (k - 1 : Nat) := by
      exact_mod_cast Nat.sub_pos_of_lt hk
    nlinarith
  have hsR : (0 : ℝ) < s := by exact_mod_cast hspos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  let z : ℝ := (s : ℝ) / n
  let p : ℝ := ((s.choose k : Nat) : ℝ) / n.choose k
  let a : ℝ := (Real.exp 1 * (c : ℝ) / y) * z ^ (k - 1)
  have hzpos : 0 < z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    exact (div_le_one hnR).2 (by exact_mod_cast hsn)
  have hzx : z ≤ cs87LocalSparsityX c k y := by
    dsimp [z]
    rw [div_le_iff₀ hnR]
    simpa [mul_comm] using hsx
  have hp : 0 < p := by
    dsimp [p]
    apply div_pos
    · exact_mod_cast Nat.choose_pos hks
    · exact_mod_cast Nat.choose_pos (hks.trans hsn)
  have hp_le : p ≤ z ^ k := by
    exact choose_ratio_le_pow_ratio hks hsn hkpos
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have henv :
      cs87Envelope c k y z = Real.exp 1 / z * a ^ y := by
    rw [cs87Envelope, cs87_alpha_eq hk]
    dsimp [a]
    rw [Real.rpow_sub hzpos, Real.rpow_one,
      Real.rpow_mul hzpos.le, Real.rpow_natCast,
      Real.mul_rpow (by positivity) (pow_nonneg hzpos.le _)]
    field_simp
  have ha1 : a ≤ 1 := by
    by_contra h
    have ha_gt : 1 < a := lt_of_not_ge h
    have hay : 1 < a ^ y := by
      simpa using Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 1) ha_gt hypos
    have hez : 1 < Real.exp 1 / z := by
      rw [one_lt_div hzpos]
      exact lt_of_le_of_lt hz1 (Real.one_lt_exp_iff.mpr (by norm_num))
    have hhalf := cs87_envelope_le_half hc hk hy hzpos.le hzx
    rw [henv] at hhalf
    nlinarith
  have hA :
      Real.exp 1 * ((c * n : Nat) : ℝ) * p / (y * s) ≤ a := by
    dsimp [a, z]
    push_cast
    calc
      Real.exp 1 * ((c : ℝ) * n) * p / (y * s) ≤
          Real.exp 1 * ((c : ℝ) * n) *
            (((s : ℝ) / n) ^ k) / (y * s) := by
              gcongr
      _ = (Real.exp 1 * (c : ℝ) / y) *
          ((s : ℝ) / n) ^ (k - 1) := by
            rw [show k = (k - 1) + 1 by omega, pow_add]
            field_simp
            congr 1
  have htail :
      ((c * n).choose R : ℝ) * p ^ R ≤ a ^ (y * s) := by
    calc
      ((c * n).choose R : ℝ) * p ^ R ≤
          (Real.exp 1 * ((c * n : Nat) : ℝ) * p /
            (y * s)) ^ (y * s) := by
              apply choose_mul_pow_le_tail_rpow hp (mul_pos hypos hsR) hR
              exact hA.trans ha1
      _ ≤ a ^ (y * s) :=
        Real.rpow_le_rpow (by positivity) hA (by positivity)
  have hchoose := choose_le_exp_mul_div_pow n s
  calc
    (n.choose s : ℝ) * (c * n).choose R * p ^ R =
        (n.choose s : ℝ) * (((c * n).choose R : ℝ) * p ^ R) := by ring
    _ ≤ (Real.exp 1 * (n : ℝ) / s) ^ s * a ^ (y * s) := by
          gcongr
    _ = (cs87Envelope c k y z) ^ s := by
          rw [henv]
          have hay : a ^ (y * (s : ℝ)) = (a ^ y) ^ s := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul ha_pos.le]
          rw [hay, ← mul_pow]
          congr 2
          dsimp [z]
          field_simp

theorem cs87_envelopeSum_le_splitMajorant {c k n : Nat} {y : ℝ}
    (hc : 0 < c) (hk : 1 < k) (hy : 1 < ((k - 1 : Nat) : ℝ) * y)
    (hn : 0 < n) (hf : cs87SmallRatio c k y n < 1) :
    cs87EnvelopeSum c k y (cs87LocalSparsityX c k y) n ≤
      cs87SplitMajorant c k y n := by
  classical
  let I : Finset Nat :=
    cs87SummationIndices n k (cs87LocalSparsityX c k y)
  let A : Finset Nat := I.filter fun s => (s : ℝ) ≤ Real.sqrt n
  let B : Finset Nat := I.filter fun s => ¬(s : ℝ) ≤ Real.sqrt n
  have hpart : ∑ s ∈ I, (cs87Envelope c k y ((s : ℝ) / n)) ^ s =
      (∑ s ∈ A, (cs87Envelope c k y ((s : ℝ) / n)) ^ s) +
      ∑ s ∈ B, (cs87Envelope c k y ((s : ℝ) / n)) ^ s := by
    simpa [A, B] using (Finset.sum_filter_add_sum_filter_not I
      (fun s : Nat => (s : ℝ) ≤ Real.sqrt n)
      (fun s => (cs87Envelope c k y ((s : ℝ) / n)) ^ s)).symm
  have hypos : 0 < y := by
    have hkpos : (0 : ℝ) < (k - 1 : Nat) := by
      exact_mod_cast (Nat.sub_pos_of_lt hk)
    nlinarith
  have hf0 : 0 ≤ cs87SmallRatio c k y n := by
    unfold cs87SmallRatio
    positivity
  have hsmall :
      (∑ s ∈ A, (cs87Envelope c k y ((s : ℝ) / n)) ^ s) ≤
        (cs87SmallRatio c k y n) ^ k /
          (1 - cs87SmallRatio c k y n) := by
    calc
      (∑ s ∈ A, (cs87Envelope c k y ((s : ℝ) / n)) ^ s) ≤
          ∑ s ∈ A, (cs87SmallRatio c k y n) ^ s := by
            apply Finset.sum_le_sum
            intro s hs
            have hsroot : (s : ℝ) ≤ Real.sqrt n :=
              (Finset.mem_filter.mp hs).2
            apply pow_le_pow_left₀ (by
              unfold cs87Envelope
              positivity)
            exact cs87_envelope_le_smallRatio hk hy hn hsroot
      _ ≤ (cs87SmallRatio c k y n) ^ k /
          (1 - cs87SmallRatio c k y n) := by
            apply finset_sum_geometric_tail_le hf0 hf k A
            intro s hs
            have hsI := (Finset.mem_filter.mp hs).1
            exact ((Finset.mem_filter.mp hsI).2).1
  have hlarge :
      (∑ s ∈ B, (cs87Envelope c k y ((s : ℝ) / n)) ^ s) ≤
        2 * (1 / 2 : ℝ) ^ n.sqrt := by
    calc
      (∑ s ∈ B, (cs87Envelope c k y ((s : ℝ) / n)) ^ s) ≤
          ∑ s ∈ B, (1 / 2 : ℝ) ^ s := by
            apply Finset.sum_le_sum
            intro s hs
            have hsI := (Finset.mem_filter.mp hs).1
            have hsIx := ((Finset.mem_filter.mp hsI).2).2
            have hnR : (0 : ℝ) < n := by exact_mod_cast hn
            have hzx : (s : ℝ) / n ≤ cs87LocalSparsityX c k y := by
              rw [div_le_iff₀ hnR]
              simpa [mul_comm] using hsIx
            apply pow_le_pow_left₀ (by
              unfold cs87Envelope
              positivity)
            exact cs87_envelope_le_half hc hk hy (by positivity) hzx
      _ ≤ (1 / 2 : ℝ) ^ n.sqrt / (1 - 1 / 2) := by
            apply finset_sum_geometric_tail_le (by norm_num) (by norm_num)
              n.sqrt B
            intro s hs
            have hnle : (n.sqrt : ℝ) ≤ Real.sqrt n := by
              apply Real.le_sqrt_of_sq_le
              exact_mod_cast (show n.sqrt ^ 2 ≤ n by
                simpa [pow_two] using Nat.sqrt_le n)
            have hsnot := (Finset.mem_filter.mp hs).2
            exact_mod_cast le_of_lt (lt_of_le_of_lt hnle (lt_of_not_ge hsnot))
      _ = 2 * (1 / 2 : ℝ) ^ n.sqrt := by ring
  rw [cs87EnvelopeSum, cs87SplitMajorant, hpart]
  exact add_le_add hsmall hlarge

theorem cs87_smallRatio_tendsto_zero {c k : Nat} {y : ℝ}
    (_hc : 0 < c) (hk : 1 < k) (hy : 1 < ((k - 1 : Nat) : ℝ) * y) :
    Tendsto (cs87SmallRatio c k y) atTop (nhds 0) := by
  have hypos : 0 < y := by
    have hkpos : (0 : ℝ) < (k - 1 : Nat) := by
      exact_mod_cast (Nat.sub_pos_of_lt hk)
    nlinarith
  have halpha : 0 < cs87Alpha k y := cs87_alpha_pos hk hy
  have hcast : Tendsto (fun n : Nat => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : Nat => ((n : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hexp : 0 < cs87Alpha k y / 2 := by positivity
  have hrpow :
      Tendsto (fun n : Nat => ((n : ℝ)⁻¹) ^ (cs87Alpha k y / 2))
        atTop (nhds 0) := by
    simpa [Real.zero_rpow hexp.ne'] using
      hinv.rpow_const (Or.inr hexp.le)
  have hrewrite : ∀ n : Nat,
      (n : ℝ) ^ (-(cs87Alpha k y) / 2) =
        ((n : ℝ)⁻¹) ^ (cs87Alpha k y / 2) := by
    intro n
    rw [show -(cs87Alpha k y) / 2 = -(cs87Alpha k y / 2) by ring,
      Real.rpow_neg (Nat.cast_nonneg n),
      ← Real.inv_rpow (Nat.cast_nonneg n)]
  convert tendsto_const_nhds.mul hrpow using 1
  · funext n
    rw [cs87SmallRatio, hrewrite]
  · simp

theorem cs87_large_tail_tendsto_zero :
    Tendsto (fun n : Nat => 2 * (1 / 2 : ℝ) ^ n.sqrt)
      atTop (nhds 0) := by
  have hsqrt : Tendsto Nat.sqrt atTop atTop := by
    refine Filter.tendsto_atTop.mpr fun b => ?_
    filter_upwards [eventually_ge_atTop (b * b)] with n hn
    exact Nat.le_sqrt.mpr hn
  have hgeom : Tendsto (fun r : Nat => (1 / 2 : ℝ) ^ r)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using tendsto_const_nhds.mul (hgeom.comp hsqrt)

theorem cs87_splitMajorant_tendsto_zero {c k : Nat} {y : ℝ}
    (hc : 0 < c) (hk : 1 < k) (hy : 1 < ((k - 1 : Nat) : ℝ) * y) :
    Tendsto (cs87SplitMajorant c k y) atTop (nhds 0) := by
  have hf := cs87_smallRatio_tendsto_zero (c := c) (k := k) (y := y) hc hk hy
  have hpow : Tendsto (fun n => (cs87SmallRatio c k y n) ^ k)
      atTop (nhds 0) := by
    simpa [zero_pow (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hk))] using hf.pow k
  have hden : Tendsto (fun n => 1 - cs87SmallRatio c k y n)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hf
  have hsmall : Tendsto
      (fun n => (cs87SmallRatio c k y n) ^ k /
        (1 - cs87SmallRatio c k y n)) atTop (nhds 0) := by
    have h := hpow.div hden (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto
      (fun n => (cs87SmallRatio c k y n) ^ k /
        (1 - cs87SmallRatio c k y n)) atTop (nhds (0 / 1)) at h
    simpa using h
  change Tendsto
    (fun n => (cs87SmallRatio c k y n) ^ k /
      (1 - cs87SmallRatio c k y n) + 2 * (1 / 2 : ℝ) ^ n.sqrt)
    atTop (nhds 0)
  simpa only [zero_add] using hsmall.add cs87_large_tail_tendsto_zero

end AvgCaseMls.Section3
