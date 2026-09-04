/-
Runnable snippet for arxiv.md, displayed with Example 4.1.

The shell exponent is `-3 + 2/(1+ε)`, below `-1` when `ε > 0`, so the p-series
converges.  Normalization and the full Levin bound are in the library.

Checked against AvgCaseMls.TR1995 and AvgCaseMls.Example41.
-/
import AvgCaseMls.TR1995
import AvgCaseMls.Example41

namespace Exposition.Example41

example (ε : ℝ) : TR1995.example41Exponent ε = -3 + 2 / (1 + ε) := rfl

theorem example41Exponent_lt_neg_one {ε : ℝ} (hε : 0 < ε) :
    TR1995.example41Exponent ε < -1 := by
  have h1 : (0 : ℝ) < 1 + ε := by linarith
  have h2 : 2 / (1 + ε) < 2 := by
    rw [div_lt_iff₀ h1]; linarith
  rw [TR1995.example41Exponent]
  linarith

theorem example_4_1 {ε : ℝ} (hε : 0 < ε) :
    Summable (TR1995.example41Contribution ε) := by
  have hp : Summable (fun n : Nat => (n : ℝ) ^ TR1995.example41Exponent ε) :=
    (Real.summable_nat_rpow).2 (example41Exponent_lt_neg_one hε)
  exact hp.mul_left (6 / Real.pi ^ 2)

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      Summable (Example41.levinShellSeries ε) ∧
      (∑' n : ℕ, Example41.levinShellSeries ε n / C) ≤ 1 :=
  Example41.normalized_levin_bound hε

example : Example41.standardDistribution.mass = 1 :=
  Example41.standardDistribution_mass

end Exposition.Example41
