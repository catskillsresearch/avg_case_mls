import AvgCaseMls.Section4.StandardUnary

/-!
# From rank-average time to unary worst-case time

The inverse-square law has support only on unary-zero strings.  A support
test rejects malformed strings, while the paper's cubic pointwise estimate
supplies polynomial fuel on every supported input.
-/

namespace AvgCaseMls.Section4

open AvgCaseMls.Foundation

namespace StandardUnary

def cubicInput (n : Nat) : Nat := (n + 1) ^ 3

theorem cubicInput_polynomial : IsPolynomial cubicInput := by
  refine .bounded 8 3 (fun n => ?_)
  change (n + 1) ^ 3 ≤ 8 * n ^ 3 + 8
  by_cases hn : n = 0
  · subst n
    norm_num
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have h12 : n ≤ n ^ 2 := Nat.le_pow (by omega)
  have h23 : n ^ 2 ≤ n ^ 3 := by
    rw [show n ^ 3 = n * n ^ 2 by ring]
    exact Nat.le_mul_of_pos_left _ hnpos
  calc
    (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring
    _ ≤ n ^ 3 + 3 * n ^ 3 + 3 * n ^ 3 + 1 := by omega
    _ ≤ 8 * n ^ 3 + 8 := by omega

def worstCaseProgram (d : Decider L) : Program :=
  .branch (.machine UnaryRank.supportTestMachine)
    d.program (.constant false [])

def worstCaseTime (T : TimeScale) (n : Nat) : Nat :=
  (2 * n + 2) + T (cubicInput n)

theorem worstCaseTime_polynomial (T : TimeScale)
    (hT : IsPolynomial T.toFun) :
    IsPolynomial (worstCaseTime T) :=
  (IsPolynomial.bounded 2 1 (fun n => by
      simp)).add (hT.comp cubicInput_polynomial)

theorem worstCaseTime_monotone (T : TimeScale) :
    Monotone (worstCaseTime T) := by
  intro a b hab
  apply Nat.add_le_add
  · omega
  · apply T.monotone
    dsimp [cubicInput]
    gcongr

/--
Any unary language whose decider is polynomial in rank-average time under the
standard inverse-square law has a concrete worst-case polynomial decider.
-/
theorem inP_of_average_of_unary {L : Set Bitstring}
    (hunary : ∀ x, x ∈ L → UnaryRank.OnSupport x)
    (haverage : InAverageP ⟨L, distribution⟩) :
    InP L := by
  obtain ⟨d, T, hT, havg⟩ := haverage
  refine ⟨worstCaseProgram d, worstCaseTime T,
    worstCaseTime_polynomial T hT, ?_⟩
  intro x
  obtain ⟨supportResult, hsupport, hsupportCorrect⟩ :=
    UnaryRank.supportTestMachine_correct x
  have hsupport' := AvgCaseMls.Foundation.eval_mono
    UnaryRank.supportTestMachine
    (show 2 * x.length + 2 ≤ worstCaseTime T (len x) by
      simp [worstCaseTime, len])
    hsupport
  by_cases hx : UnaryRank.OnSupport x
  · have haccept : supportResult.accept = true :=
      hsupportCorrect.mpr hx
    have hxcode : x = UnaryRank.code x.length := hx
    have hruntime :
        d.actualRuntime x ≤ T (cubicInput x.length) := by
      rw [hxcode]
      simpa [cubicInput, UnaryRank.code] using
        runtime_le_scale_cubic d T havg x.length
    have hdExact :
        d.program.eval (d.actualRuntime x) x = some (d.actualResult x) :=
      d.program.eval_at_steps (d.actualResult_spec x)
    have hfuel :
        d.actualRuntime x ≤ worstCaseTime T (len x) := by
      exact hruntime.trans
        (Nat.le_add_left _ (2 * x.length + 2))
    have hdLarge := d.program.eval_mono hfuel hdExact
    have hdLarge' :
        d.program.eval (worstCaseTime T x.length) x =
          some (d.actualResult x) := by
      simpa [len] using hdLarge
    refine ⟨{
      d.actualResult x with
      steps := supportResult.steps + (d.actualResult x).steps
    }, ?_, ?_⟩
    · simp only [worstCaseProgram, Program.eval]
      rw [hsupport']
      simp [haccept, hdLarge']
    · exact d.actualResult_correct x
  · have haccept : supportResult.accept = false := by
      cases h : supportResult.accept
      · rfl
      · exact False.elim (hx (hsupportCorrect.mp h))
    refine ⟨⟨false, [], supportResult.steps + 1⟩, ?_, ?_⟩
    · simp only [worstCaseProgram, Program.eval]
      rw [hsupport']
      simp [haccept]
    · simp only [Bool.false_eq_true, false_iff]
      exact fun hL => hx (hunary x hL)

end StandardUnary

end AvgCaseMls.Section4
