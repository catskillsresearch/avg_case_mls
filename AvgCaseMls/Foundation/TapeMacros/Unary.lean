import AvgCaseMls.Foundation.TapeMacros.Scan

/-!
# Primitive unary padding machines

These fixed machines use only base tape instructions.  They implement one
unary padding step and its inverse on nonempty words.
-/

namespace AvgCaseMls.Foundation.TapeMacros

open AvgCaseMls.Foundation

def appendZeroMachine : Machine :=
  ⟨#[.branch 2 1 1, .moveRight 0, .write (some false) 3, .halt true]⟩

private theorem appendZero_step (left : List TapeSymbol) (b : Bool)
    (bs : Bitstring) (fuel elapsed : Nat) :
    evalFrom appendZeroMachine (fuel + 2)
        (blockConfig left (b :: bs)) elapsed =
      evalFrom appendZeroMachine fuel
        (blockConfig (some b :: left) bs) (elapsed + 2) := by
  cases b <;> cases bs <;>
    simp [blockConfig, appendZeroMachine, evalFrom, step, moveRight]

theorem appendZero_from (left : List TapeSymbol) (xs : Bitstring)
    (elapsed : Nat) :
    evalFrom appendZeroMachine (2 * xs.length + 3)
        (blockConfig left xs) elapsed =
      some ⟨true, left.reverse.filterMap id ++ xs ++ [false],
        elapsed + (2 * xs.length + 3)⟩ := by
  induction xs generalizing left elapsed with
  | nil =>
      simp [blockConfig, appendZeroMachine, evalFrom, step, tapeOutput]
  | cons b bs ih =>
      rw [show 2 * (b :: bs).length + 3 =
        (2 * bs.length + 3) + 2 by simp; omega]
      rw [appendZero_step]
      rw [ih]
      congr 2
      · simp [List.filterMap_reverse, List.append_assoc]
      · omega

theorem appendZero_correct :
    ComputesExactly appendZeroMachine (fun x => x ++ [false])
      (fun x => 2 * x.length + 3) := by
  intro x
  change evalFrom appendZeroMachine (2 * x.length + 3)
      (blockConfig [] x) 0 =
    some ⟨true, x ++ [false], 2 * x.length + 3⟩
  simpa using appendZero_from [] x 0

def appendZeroTime (n : Nat) : Nat := 2 * n + 3

theorem appendZeroTime_polynomial : IsPolynomial appendZeroTime :=
  .bounded 3 1 (fun n => by simp [appendZeroTime]; omega)

theorem appendZeroTime_monotone : Monotone appendZeroTime := by
  intro a b hab
  simp [appendZeroTime]
  omega

theorem appendZero_computes :
    ComputesWithin (.machine appendZeroMachine) (fun x => x ++ [false])
      appendZeroTime := by
  intro x
  exact ⟨⟨true, x ++ [false], appendZeroTime x.length⟩,
    appendZero_correct x, rfl⟩

@[simp] theorem appendZero_unary (n : Nat) :
    List.replicate n false ++ [false] = List.replicate (n + 1) false := by
  induction n with
  | zero => simp
  | succ n ih =>
      simpa [List.replicate_succ, ih, Nat.add_assoc]

end AvgCaseMls.Foundation.TapeMacros
