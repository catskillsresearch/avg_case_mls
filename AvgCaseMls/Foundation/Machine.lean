/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits

/-!
An executable deterministic two-stack tape machine over bitstrings.

The tape alphabet is `blank`, `0`, and `1`.  The cells left of the head are
stored in reverse order in `left`; the current cell and cells to its right are
stored separately.  Thus left and right moves, reads, and writes are constant
time operations.  This is the standard two-stack presentation of a
single-tape Turing machine and is Turing-complete.
-/

namespace AvgCaseMls.Foundation

abbrev Bitstring := List Bool

abbrev TapeSymbol := Option Bool

inductive Instruction where
  | halt (accept : Bool)
  | jump (next : Nat)
  | branch (onBlank onFalse onTrue : Nat)
  | write (symbol : TapeSymbol) (next : Nat)
  | moveLeft (next : Nat)
  | moveRight (next : Nat)
  deriving DecidableEq, Repr

structure Machine where
  code : Array Instruction
  deriving DecidableEq, Repr

structure Config where
  pc : Nat
  left : List TapeSymbol
  head : TapeSymbol
  right : List TapeSymbol
  deriving DecidableEq, Repr

structure Result where
  accept : Bool
  output : Bitstring
  steps : Nat
  deriving DecidableEq, Repr

/--
Input convention: the head starts on the first bit, with blanks elsewhere.
The empty input starts on a blank cell.
-/
def initial (input : Bitstring) : Config :=
  match input with
  | [] => ⟨0, [], none, []⟩
  | bit :: rest => ⟨0, [], some bit, rest.map some⟩

/--
Output convention: read represented nonblank cells from left to right,
discarding blanks.  In particular a machine that immediately halts outputs its
input unchanged.
-/
def tapeOutput (c : Config) : Bitstring :=
  (c.left.reverse ++ c.head :: c.right).filterMap id

def moveLeft (c : Config) (next : Nat) : Config :=
  match c.left with
  | [] => ⟨next, [], none, c.head :: c.right⟩
  | symbol :: left => ⟨next, left, symbol, c.head :: c.right⟩

def moveRight (c : Config) (next : Nat) : Config :=
  match c.right with
  | [] => ⟨next, c.head :: c.left, none, []⟩
  | symbol :: right => ⟨next, c.head :: c.left, symbol, right⟩

def step (M : Machine) (c : Config) : Except Result Config :=
  match M.code[c.pc]? with
  | none => .error ⟨false, tapeOutput c, 0⟩
  | some (.halt accept) => .error ⟨accept, tapeOutput c, 0⟩
  | some (.jump next) => .ok { c with pc := next }
  | some (.branch onBlank onFalse onTrue) =>
      match c.head with
      | none => .ok { c with pc := onBlank }
      | some false => .ok { c with pc := onFalse }
      | some true => .ok { c with pc := onTrue }
  | some (.write symbol next) => .ok { c with pc := next, head := symbol }
  | some (.moveLeft next) => .ok (moveLeft c next)
  | some (.moveRight next) => .ok (moveRight c next)

/-- Execute at most `fuel` transitions.  A halt instruction consumes one step. -/
def evalFrom (M : Machine) : Nat → Config → Nat → Option Result
  | 0, _, _ => none
  | fuel + 1, c, elapsed =>
      match step M c with
      | .error r => some { r with steps := elapsed + 1 }
      | .ok c' => evalFrom M fuel c' (elapsed + 1)

def eval (M : Machine) (fuel : Nat) (input : Bitstring) : Option Result :=
  evalFrom M fuel (initial input) 0

theorem evalFrom_mono (M : Machine) {fuel₁ fuel₂ : Nat} (h : fuel₁ ≤ fuel₂)
    {c : Config} {elapsed : Nat} {r : Result}
    (hr : evalFrom M fuel₁ c elapsed = some r) :
    evalFrom M fuel₂ c elapsed = some r := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction fuel₁ generalizing c elapsed with
  | zero =>
      change none = some r at hr
      contradiction
  | succ fuel ih =>
      rw [Nat.succ_add]
      simp only [evalFrom] at hr ⊢
      cases hstep : step M c with
      | error result =>
          simp only [hstep] at hr ⊢
          exact hr
      | ok config =>
          simp only [hstep] at hr ⊢
          exact ih hr

theorem eval_mono (M : Machine) {fuel₁ fuel₂ : Nat} (h : fuel₁ ≤ fuel₂)
    {input : Bitstring} {r : Result} (hr : eval M fuel₁ input = some r) :
    eval M fuel₂ input = some r :=
  evalFrom_mono M h hr

/--
Successful low-level runs can be replayed with exactly their recorded
transition count.  This connects the executable fuel semantics to average
time, which is defined using `Result.steps`.
-/
theorem evalFrom_at_steps (M : Machine) {fuel : Nat} {c : Config}
    {elapsed : Nat} {r : Result}
    (hr : evalFrom M fuel c elapsed = some r) :
    elapsed < r.steps ∧ evalFrom M (r.steps - elapsed) c elapsed = some r := by
  induction fuel generalizing c elapsed with
  | zero => simp [evalFrom] at hr
  | succ fuel ih =>
      simp only [evalFrom] at hr
      cases hstep : step M c with
      | error result =>
          simp only [hstep, Option.some.injEq] at hr
          subst r
          simp [evalFrom, hstep]
      | ok config =>
          simp only [hstep] at hr
          obtain ⟨hlt, hreplay⟩ := ih hr
          constructor
          · omega
          · rw [show r.steps - elapsed = (r.steps - (elapsed + 1)) + 1 by omega]
            simp only [evalFrom, hstep]
            exact hreplay

theorem eval_at_steps (M : Machine) {fuel : Nat} {input : Bitstring}
    {r : Result} (hr : eval M fuel input = some r) :
    eval M r.steps input = some r := by
  exact (evalFrom_at_steps M hr).2

/-- Executable runtime observation; `none` means the fuel was exhausted. -/
def runtime (M : Machine) (fuel : Nat) (input : Bitstring) : Option Nat :=
  (eval M fuel input).map Result.steps

/-- Canonical self-delimiting binary natural encoding used by program outputs. -/
def encodeNat (n : Nat) : Bitstring :=
  let payload := Nat.bits n
  List.replicate payload.length true ++ false :: payload

/--
Executable programs close the low-level tape machines under sequential
composition.  Both components receive the same fuel allowance; consequently
a composed polynomial-time bound only has to dominate the two component
bounds.  The second component is run on the first component's output.
-/
inductive Program where
  | machine (machine : Machine)
  | constant (accept : Bool) (output : Bitstring)
  | encodeLength
  | compose (first second : Program)
  | branch (condition whenTrue whenFalse : Program)

namespace Program

def eval : Program → Nat → Bitstring → Option Result
  | .machine M, fuel, input => AvgCaseMls.Foundation.eval M fuel input
  | .constant accept output, _, _ => some ⟨accept, output, 1⟩
  | .encodeLength, _, input => some ⟨true, encodeNat input.length, input.length + 1⟩
  | .compose first second, fuel, input => do
      let firstResult ← first.eval fuel input
      let secondResult ← second.eval fuel firstResult.output
      pure { secondResult with steps := firstResult.steps + secondResult.steps }
  | .branch condition whenTrue whenFalse, fuel, input => do
      let conditionResult ← condition.eval fuel input
      let branchResult ←
        if conditionResult.accept then whenTrue.eval fuel input
        else whenFalse.eval fuel input
      pure { branchResult with steps := conditionResult.steps + branchResult.steps }

@[simp] theorem eval_machine (M : Machine) (fuel : Nat) (input : Bitstring) :
    (Program.machine M).eval fuel input =
      AvgCaseMls.Foundation.eval M fuel input := rfl

theorem eval_mono (program : Program) {fuel₁ fuel₂ : Nat} (h : fuel₁ ≤ fuel₂)
    {input : Bitstring} {r : Result} (hr : program.eval fuel₁ input = some r) :
    program.eval fuel₂ input = some r := by
  induction program generalizing input r with
  | machine M => exact AvgCaseMls.Foundation.eval_mono M h hr
  | constant accept output => exact hr
  | encodeLength => exact hr
  | compose first second ihFirst ihSecond =>
      simp only [eval] at hr ⊢
      cases hfirst : first.eval fuel₁ input with
      | none => simp [hfirst] at hr
      | some firstResult =>
          have hfirst' := ihFirst hfirst
          rw [hfirst']
          cases hsecond : second.eval fuel₁ firstResult.output with
          | none => simp [hfirst, hsecond] at hr
          | some secondResult =>
              have hsecond' := ihSecond hsecond
              simpa [hfirst, hfirst', hsecond, hsecond'] using hr
  | branch condition whenTrue whenFalse ihCondition ihTrue ihFalse =>
      simp only [eval] at hr ⊢
      cases hcondition : condition.eval fuel₁ input with
      | none => simp [hcondition] at hr
      | some conditionResult =>
          have hcondition' := ihCondition hcondition
          rw [hcondition']
          cases hc : conditionResult.accept
          · cases hfalse : whenFalse.eval fuel₁ input with
            | none => simp [hcondition, hc, hfalse] at hr
            | some branchResult =>
                have hfalse' := ihFalse hfalse
                simpa [hcondition, hcondition', hc, hfalse, hfalse'] using hr
          · cases htrue : whenTrue.eval fuel₁ input with
            | none => simp [hcondition, hc, htrue] at hr
            | some branchResult =>
                have htrue' := ihTrue htrue
                simpa [hcondition, hcondition', hc, htrue, htrue'] using hr

theorem eval_at_steps (program : Program) {fuel : Nat} {input : Bitstring}
    {r : Result} (hr : program.eval fuel input = some r) :
    program.eval r.steps input = some r := by
  induction program generalizing input r with
  | machine M => exact AvgCaseMls.Foundation.eval_at_steps M hr
  | constant accept output => simpa [eval] using hr
  | encodeLength => simpa [eval] using hr
  | compose first second ihFirst ihSecond =>
      simp only [eval] at hr ⊢
      cases hfirst : first.eval fuel input with
      | none => simp [hfirst] at hr
      | some firstResult =>
          cases hsecond : second.eval fuel firstResult.output with
          | none => simp [hfirst, hsecond] at hr
          | some secondResult =>
              have hr' : r =
                  { secondResult with
                    steps := firstResult.steps + secondResult.steps } := by
                simpa [hfirst, hsecond] using hr.symm
              subst r
              have hfirstExact := ihFirst hfirst
              have hsecondExact := ihSecond hsecond
              have hfirstLarge := first.eval_mono
                (Nat.le_add_right firstResult.steps secondResult.steps) hfirstExact
              have hsecondLarge := second.eval_mono
                (Nat.le_add_left secondResult.steps firstResult.steps) hsecondExact
              simp [hfirstLarge, hsecondLarge]
  | branch condition whenTrue whenFalse ihCondition ihTrue ihFalse =>
      simp only [eval] at hr ⊢
      cases hcondition : condition.eval fuel input with
      | none => simp [hcondition] at hr
      | some conditionResult =>
          cases hc : conditionResult.accept
          · cases hfalse : whenFalse.eval fuel input with
            | none => simp [hcondition, hc, hfalse] at hr
            | some branchResult =>
                have hr' : r =
                    { branchResult with
                      steps := conditionResult.steps + branchResult.steps } := by
                  simpa [hcondition, hc, hfalse] using hr.symm
                subst r
                have hconditionExact := ihCondition hcondition
                have hfalseExact := ihFalse hfalse
                have hconditionLarge := condition.eval_mono
                  (Nat.le_add_right conditionResult.steps branchResult.steps)
                  hconditionExact
                have hfalseLarge := whenFalse.eval_mono
                  (Nat.le_add_left branchResult.steps conditionResult.steps)
                  hfalseExact
                simp [hconditionLarge, hc, hfalseLarge]
          · cases htrue : whenTrue.eval fuel input with
            | none => simp [hcondition, hc, htrue] at hr
            | some branchResult =>
                have hr' : r =
                    { branchResult with
                      steps := conditionResult.steps + branchResult.steps } := by
                  simpa [hcondition, hc, htrue] using hr.symm
                subst r
                have hconditionExact := ihCondition hcondition
                have htrueExact := ihTrue htrue
                have hconditionLarge := condition.eval_mono
                  (Nat.le_add_right conditionResult.steps branchResult.steps)
                  hconditionExact
                have htrueLarge := whenTrue.eval_mono
                  (Nat.le_add_left branchResult.steps conditionResult.steps)
                  htrueExact
                simp [hconditionLarge, hc, htrueLarge]

end Program

@[simp] theorem tapeOutput_initial (input : Bitstring) :
    tapeOutput (initial input) = input := by
  cases input <;> simp [initial, tapeOutput]

@[simp] theorem eval_zero (M : Machine) (input : Bitstring) :
    eval M 0 input = none := rfl

@[simp] theorem runtime_zero (M : Machine) (input : Bitstring) :
    runtime M 0 input = none := rfl

end AvgCaseMls.Foundation
