import AvgCaseMls.Foundation.Universal.Encoding

namespace AvgCaseMls.Foundation.Universal

open AvgCaseMls.Foundation

/-- Exact finite execution, stopping before a halting transition. -/
inductive Runs (machine : Machine) : Config → Nat → Config → Prop
  | refl (config : Config) : Runs machine config 0 config
  | next {config next result : Config} {steps : Nat}
      (hstep : step machine config = .ok next)
      (tail : Runs machine next steps result) :
      Runs machine config (steps + 1) result

theorem Runs.trans {machine : Machine} {first middle last : Config}
    {m n : Nat} (h₁ : Runs machine first m middle)
    (h₂ : Runs machine middle n last) :
    Runs machine first (m + n) last := by
  induction h₁ with
  | refl => simpa using h₂
  | next hstep tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm 1 n] using
        (Runs.next hstep (ih h₂))

theorem Runs.evalFrom_eq {machine : Machine} {first last : Config}
    {steps : Nat} (hrun : Runs machine first steps last)
    (fuel elapsed : Nat) :
    evalFrom machine (steps + fuel) first elapsed =
      evalFrom machine fuel last (elapsed + steps) := by
  induction hrun generalizing elapsed with
  | refl => simp
  | next hstep tail ih =>
      rw [Nat.add_assoc, Nat.add_comm 1 fuel, ← Nat.add_assoc]
      simp only [evalFrom, hstep]
      convert ih (elapsed + 1) using 1 <;> ac_rfl

theorem Runs.halt {machine : Machine} {first last : Config} {steps elapsed : Nat}
    {result : Result} (hrun : Runs machine first steps last)
    (hhalt : step machine last = .error result) :
    evalFrom machine (steps + 1) first elapsed =
      some { result with steps := elapsed + steps + 1 } := by
  rw [hrun.evalFrom_eq 1 elapsed]
  simp [evalFrom, hhalt, Nat.add_assoc]

end AvgCaseMls.Foundation.Universal
