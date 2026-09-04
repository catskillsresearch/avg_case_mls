import AvgCaseMls.Foundation.TapeMacros.Arithmetic

/-!
# Delimited-block routines

A blank cell delimits a block.  These routines are closed finite control
graphs, not evaluator extensions.
-/

namespace AvgCaseMls.Foundation.TapeMacros

open AvgCaseMls.Foundation

def eraseBits (_ : Bitstring) : Bitstring := []
def eraseSteps (bits : Bitstring) : Nat := 3 * bits.length + 2

def eraseFragment : Fragment :=
  [.branch (.local 3) (.local 1) (.local 1),
   .write none (.local 2),
   .moveRight (.local 0),
   .halt true]

def eraseMachine : Machine := eraseFragment.machine

private theorem erase_step (left : List TapeSymbol) (bit : Bool)
    (rest : Bitstring) (fuel elapsed : Nat) :
    evalFrom eraseMachine (fuel + 3)
        (blockConfig left (bit :: rest)) elapsed =
      evalFrom eraseMachine fuel
        (blockConfig (none :: left) rest) (elapsed + 3) := by
  cases bit <;> cases rest <;>
    simp [eraseMachine, eraseFragment, Fragment.machine, Fragment.compileAt,
      Asm.compile, Target.resolve, blockConfig, evalFrom, step, moveRight]

theorem erase_from (left : List TapeSymbol) (bits : Bitstring)
    (elapsed : Nat) :
    evalFrom eraseMachine (eraseSteps bits) (blockConfig left bits) elapsed =
      some ⟨true, left.reverse.filterMap id,
        elapsed + eraseSteps bits⟩ := by
  induction bits generalizing left elapsed with
  | nil =>
      simp [eraseMachine, eraseFragment, Fragment.machine, Fragment.compileAt,
        Asm.compile, Target.resolve, eraseSteps, blockConfig, evalFrom, step,
        tapeOutput]
  | cons bit rest ih =>
      rw [show eraseSteps (bit :: rest) = eraseSteps rest + 3 by
        simp [eraseSteps]; omega]
      rw [erase_step, ih]
      congr 2
      · simp [List.filterMap_reverse]
      · omega

theorem erase_correct :
    ComputesExactly eraseMachine eraseBits eraseSteps := by
  intro bits
  change evalFrom eraseMachine (eraseSteps bits) (blockConfig [] bits) 0 =
    some ⟨true, eraseBits bits, eraseSteps bits⟩
  simpa [eraseBits] using erase_from [] bits 0

def appendBitFragment (bit : Bool) : Fragment :=
  [.branch (.local 2) (.local 1) (.local 1),
   .moveRight (.local 0),
   .write (some bit) (.local 3),
   .halt true]

def appendBitMachine (bit : Bool) : Machine := (appendBitFragment bit).machine
def appendBitSteps (bits : Bitstring) : Nat := 2 * bits.length + 3

private theorem appendBit_step (left : List TapeSymbol) (head : Bool)
    (rest : Bitstring) (bit : Bool) (fuel elapsed : Nat) :
    evalFrom (appendBitMachine bit) (fuel + 2)
        (blockConfig left (head :: rest)) elapsed =
      evalFrom (appendBitMachine bit) fuel
        (blockConfig (some head :: left) rest) (elapsed + 2) := by
  cases head <;> cases rest <;> cases bit <;>
    simp [appendBitMachine, appendBitFragment, Fragment.machine,
      Fragment.compileAt, Asm.compile, Target.resolve, blockConfig,
      evalFrom, step, moveRight]

theorem appendBit_from (left : List TapeSymbol) (bits : Bitstring)
    (bit : Bool) (elapsed : Nat) :
    evalFrom (appendBitMachine bit) (appendBitSteps bits)
        (blockConfig left bits) elapsed =
      some ⟨true, left.reverse.filterMap id ++ bits ++ [bit],
        elapsed + appendBitSteps bits⟩ := by
  induction bits generalizing left elapsed with
  | nil =>
      cases bit <;>
        simp [appendBitMachine, appendBitFragment, Fragment.machine,
          Fragment.compileAt, Asm.compile, Target.resolve, appendBitSteps,
          blockConfig, evalFrom, step, tapeOutput]
  | cons head rest ih =>
      rw [show appendBitSteps (head :: rest) = appendBitSteps rest + 2 by
        simp [appendBitSteps]; omega]
      rw [appendBit_step, ih]
      congr 2
      · simp [List.filterMap_reverse, List.append_assoc]
      · omega

theorem appendBit_correct (bit : Bool) :
    ComputesExactly (appendBitMachine bit) (fun bits => bits ++ [bit])
      appendBitSteps := by
  intro bits
  change evalFrom (appendBitMachine bit) (appendBitSteps bits)
      (blockConfig [] bits) 0 =
    some ⟨true, bits ++ [bit], appendBitSteps bits⟩
  simpa using appendBit_from [] bits bit 0

/--
Turn a body whose exit means "continue" into a blank-delimited loop.  The
closing halt is the only loop exit.
-/
def loopDelimited (body : Fragment) : Fragment :=
  [.branch (.local (body.length + 1)) (.local 1) (.local 1)] ++
    (body.map (Asm.shiftLocals 1)).map (Asm.retarget (.local 0)) ++
    [.halt true]

@[simp] theorem loopDelimited_length (body : Fragment) :
    (loopDelimited body).length = body.length + 2 := by
  simp [loopDelimited]

def copyBlock (bits : Bitstring) : Bitstring := bits ++ bits
def copyBound (n : Nat) : Nat := 8 * n * n + 12 * n + 4
def appendBlock (first second : Bitstring) : Bitstring := first ++ second
def appendBound (m n : Nat) : Nat := 6 * (m + n) + 4

theorem copyBound_polynomial : IsPolynomial copyBound :=
  .bounded 24 2 (fun n => by simp [copyBound]; nlinarith)

theorem appendBound_polynomial (m : Nat) :
    IsPolynomial (fun n => appendBound m n) :=
  .bounded (6 * m + 10) 1 (fun n => by
    simp [appendBound]
    nlinarith)

@[simp] theorem eraseFragment_wellFormed : eraseFragment.wellFormed := by
  simp [Fragment.wellFormed, eraseFragment, Asm.wellFormed,
    Target.wellFormed]

@[simp] theorem appendBitFragment_wellFormed (bit : Bool) :
    (appendBitFragment bit).wellFormed := by
  cases bit <;>
    simp [Fragment.wellFormed, appendBitFragment, Asm.wellFormed,
      Target.wellFormed]

end AvgCaseMls.Foundation.TapeMacros
