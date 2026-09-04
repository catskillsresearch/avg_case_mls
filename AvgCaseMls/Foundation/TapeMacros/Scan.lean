import AvgCaseMls.Foundation.TapeMacros.Core

/-!
# Verified delimiter scanning

The tape blank is the block delimiter.  `scanBlankMachine` walks right across
one binary block and halts on its terminating blank without changing the tape.
-/

namespace AvgCaseMls.Foundation.TapeMacros

open AvgCaseMls.Foundation

def blockConfig (left : List TapeSymbol) : Bitstring → Config
  | [] => ⟨0, left, none, []⟩
  | b :: bs => ⟨0, left, some b, bs.map some⟩

def scanBlankMachine : Machine :=
  ⟨#[.branch 2 1 1, .moveRight 0, .halt true]⟩

private theorem scanBlank_step (left : List TapeSymbol) (b : Bool)
    (bs : Bitstring) (fuel elapsed : Nat) :
    evalFrom scanBlankMachine (fuel + 2)
        (blockConfig left (b :: bs)) elapsed =
      evalFrom scanBlankMachine fuel
        (blockConfig (some b :: left) bs) (elapsed + 2) := by
  cases b <;> cases bs <;>
    simp [blockConfig, scanBlankMachine, evalFrom, step, moveRight]

theorem scanBlank_from (left : List TapeSymbol) (xs : Bitstring)
    (elapsed : Nat) :
    evalFrom scanBlankMachine (2 * xs.length + 2)
        (blockConfig left xs) elapsed =
      some ⟨true, left.reverse.filterMap id ++ xs,
        elapsed + (2 * xs.length + 2)⟩ := by
  induction xs generalizing left elapsed with
  | nil =>
      simp [blockConfig, scanBlankMachine, evalFrom, step, tapeOutput]
  | cons b bs ih =>
      rw [show 2 * (b :: bs).length + 2 =
        (2 * bs.length + 2) + 2 by simp; omega]
      rw [scanBlank_step]
      rw [ih]
      congr 2
      · simp [List.filterMap_reverse, List.append_assoc]
      · omega

theorem scanBlank_correct :
    ComputesExactly scanBlankMachine id (fun x => 2 * x.length + 2) := by
  intro x
  change evalFrom scanBlankMachine (2 * x.length + 2)
      (blockConfig [] x) 0 =
    some ⟨true, id x, 2 * x.length + 2⟩
  simpa using scanBlank_from [] x 0

theorem scanBlank_output_length (x : Bitstring) :
    (id x).length = x.length := rfl

def scanBlankTime (n : Nat) : Nat := 2 * n + 2

theorem scanBlankTime_polynomial : IsPolynomial scanBlankTime :=
  .bounded 2 1 (fun n => by simp [scanBlankTime])

theorem scanBlankTime_monotone : Monotone scanBlankTime := by
  intro a b hab
  simp [scanBlankTime]
  omega

theorem scanBlank_computes :
    ComputesWithin (.machine scanBlankMachine) id scanBlankTime := by
  intro x
  exact ⟨⟨true, x, scanBlankTime x.length⟩,
    scanBlank_correct x, rfl⟩

end AvgCaseMls.Foundation.TapeMacros
