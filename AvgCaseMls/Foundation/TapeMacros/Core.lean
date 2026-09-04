import AvgCaseMls.Foundation.Rankability

/-!
# Shared correctness interfaces for low-level tape macros

Every primitive macro in this directory is an actual `Machine`: its execution
goes exclusively through `Instruction`, `step`, and `evalFrom`.  This file
contains only proof-level interfaces and closure lemmas; it adds no evaluator
primitive.
-/

namespace AvgCaseMls.Foundation.TapeMacros

open AvgCaseMls.Foundation

/-- Exact functional correctness, including the transition count. -/
def ComputesExactly (M : Machine) (f : Bitstring → Bitstring)
    (steps : Bitstring → Nat) : Prop :=
  ∀ x, eval M (steps x) x = some ⟨true, f x, steps x⟩

/--
Sequential composition with a common explicit fuel allowance.  The evaluator
records the sum of the two exact runtimes.
-/
theorem compose_eval {p q : Program} {f g : Bitstring → Bitstring}
    {Tp Tq : Nat → Nat}
    (hp : ComputesWithin p f Tp) (hq : ComputesWithin q g Tq)
    (hTq : Monotone Tq)
    (lengthBound : Nat → Nat) (hlen : ∀ x, len (f x) ≤ lengthBound (len x))
    (x : Bitstring) :
    let fuel := Tp (len x) + Tq (lengthBound (len x))
    ∃ rp rq,
      p.eval fuel x = some rp ∧
      q.eval fuel (f x) = some rq ∧
      (Program.compose p q).eval fuel x =
        some { rq with steps := rp.steps + rq.steps } ∧
      rq.output = g (f x) := by
  dsimp
  obtain ⟨rp, hpRun, hpOut⟩ := hp x
  obtain ⟨rq, hqRun, hqOut⟩ := hq (f x)
  let fuel := Tp (len x) + Tq (lengthBound (len x))
  have hpFuel : Tp (len x) ≤ fuel := Nat.le_add_right _ _
  have hqFuel : Tq (len (f x)) ≤ fuel := by
    exact (hTq (hlen x)).trans (Nat.le_add_left _ _)
  have hpRun' := Program.eval_mono p hpFuel hpRun
  have hqRun' := Program.eval_mono q hqFuel hqRun
  refine ⟨rp, rq, hpRun', hqRun', ?_, hqOut⟩
  dsimp [fuel] at hpRun' hqRun'
  simp [Program.eval, hpRun', hpOut, hqRun']

theorem compose_computesWithin {p q : Program} {f g : Bitstring → Bitstring}
    {Tp Tq lengthBound : Nat → Nat}
    (hp : ComputesWithin p f Tp) (hq : ComputesWithin q g Tq)
    (hTq : Monotone Tq)
    (hlen : ∀ x, len (f x) ≤ lengthBound (len x)) :
    ComputesWithin (.compose p q) (g ∘ f)
      (fun n => Tp n + Tq (lengthBound n)) := by
  intro x
  obtain ⟨rp, rq, _, _, hrun, hout⟩ :=
    compose_eval hp hq hTq lengthBound hlen x
  exact ⟨{ rq with steps := rp.steps + rq.steps }, hrun, hout⟩

theorem compose_polynomialFuel {Tp Tq lengthBound : Nat → Nat}
    (hp : IsPolynomial Tp) (hq : IsPolynomial Tq)
    (hlen : IsPolynomial lengthBound) :
    IsPolynomial (fun n => Tp n + Tq (lengthBound n)) :=
  hp.add (hq.comp hlen)

/--
Adding polynomial preprocessing to a single-exponential second stage remains
single-exponential.  This intentionally exposes the concrete composed fuel.
-/
theorem compose_exponentialFuel {Tp Tq lengthBound : Nat → Nat}
    (hp : IsPolynomial Tp) (hq : IsExponential Tq)
    (hlen : IsPolynomial lengthBound) :
    IsExponential (fun n => Tp n + Tq (lengthBound n)) := by
  rcases hq with ⟨q, c, hqPoly, hc, hqBound⟩
  let exponent := fun n => Tp n + q (lengthBound n)
  refine ⟨exponent, c + 1,
    hp.add (hqPoly.comp hlen), by omega, ?_⟩
  intro n
  have hsecond := hqBound (lengthBound n)
  have hlePow : ∀ m : Nat, m ≤ 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ]
        have hpos : 0 < 2 ^ m := pow_pos (by omega : 0 < (2 : Nat)) m
        omega
  have hTp : Tp n ≤ 2 ^ Tp n := hlePow _
  have hpow₁ : 2 ^ Tp n ≤ 2 ^ exponent n := by
    apply Nat.pow_le_pow_right (by omega)
    simp [exponent]
  have hpow₂ : 2 ^ q (lengthBound n) ≤ 2 ^ exponent n := by
    apply Nat.pow_le_pow_right (by omega)
    simp [exponent]
  calc
    Tp n + Tq (lengthBound n)
        ≤ 2 ^ exponent n + (c * 2 ^ exponent n + c) := by
          exact Nat.add_le_add (hTp.trans hpow₁)
            (hsecond.trans (Nat.add_le_add_right
              (Nat.mul_le_mul_left c hpow₂) c))
    _ ≤ (c + 1) * 2 ^ exponent n + (c + 1) := by
      rw [Nat.add_mul]
      omega

end AvgCaseMls.Foundation.TapeMacros
