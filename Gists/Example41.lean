/-
Runnable gist for arxiv.md, displayed with Example 4.1.

The report's Example 4.1 puts the standard law
`μ(x) = (6/π²)|x|⁻² 2^(-|x|)` against a decider running in `|x|²` steps and
claims Levin average time `O(n^(1+ε))`.  Summing the Levin cost over the shell
of length `n` cancels the `2^(-n)`, leaving `(6/π²) n^(-3 + 2/(1+ε))`.  The
exponent is below `-1` exactly when `ε > 0`, so the series converges by
comparison with a p-series.

Convergence is not the same as being bounded by `1`, which is what the Levin
condition demands, so a normalizing constant is genuinely needed; the paper
discusses why.

Checked against AvgCaseMls.TR1995 and AvgCaseMls.Example41.
-/
import AvgCaseMls.TR1995
import AvgCaseMls.Example41

namespace Gists.Example41

/-! ## The shell exponent -/

/-- `-3 + 2/(1+ε)`: two from the inverse time scale, minus three from the
density and the `1/|x|` weight. -/
example (ε : ℝ) : TR1995.example41Exponent ε = -3 + 2 / (1 + ε) := rfl

/-- It drops below `-1` precisely because `2/(1+ε) < 2` when `ε > 0`. -/
theorem example41Exponent_lt_neg_one {ε : ℝ} (hε : 0 < ε) :
    TR1995.example41Exponent ε < -1 := by
  have h1 : (0 : ℝ) < 1 + ε := by linarith
  have h2 : 2 / (1 + ε) < 2 := by
    rw [div_lt_iff₀ h1]; linarith
  rw [TR1995.example41Exponent]
  linarith

/-! ## Convergence -/

/-- Example 4.1: the shell contributions are summable. -/
theorem example_4_1 {ε : ℝ} (hε : 0 < ε) :
    Summable (TR1995.example41Contribution ε) := by
  -- A p-series with exponent below `-1`, scaled by the density constant.
  have hp : Summable (fun n : Nat => (n : ℝ) ^ TR1995.example41Exponent ε) :=
    (Real.summable_nat_rpow).2 (example41Exponent_lt_neg_one hε)
  exact hp.mul_left (6 / Real.pi ^ 2)

/-! ## The normalization the report's `O(·)` hides

The Levin condition requires the weighted sum to be at most `1`, so the
constant is chosen as `max S 1` where `S` is the total. -/

example {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      Summable (Example41.levinShellSeries ε) ∧
      (∑' n : ℕ, Example41.levinShellSeries ε n / C) ≤ 1 :=
  Example41.normalized_levin_bound hε

/-- The law really is a probability measure: `∑ n⁻² = π²/6` normalizes it. -/
example : Example41.standardDistribution.mass = 1 :=
  Example41.standardDistribution_mass

end Gists.Example41
