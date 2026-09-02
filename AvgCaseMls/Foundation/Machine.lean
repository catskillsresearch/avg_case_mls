/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import Mathlib.Data.List.Basic

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

/-- Executable runtime observation; `none` means the fuel was exhausted. -/
def runtime (M : Machine) (fuel : Nat) (input : Bitstring) : Option Nat :=
  (eval M fuel input).map Result.steps

@[simp] theorem tapeOutput_initial (input : Bitstring) :
    tapeOutput (initial input) = input := by
  cases input <;> simp [initial, tapeOutput]

@[simp] theorem eval_zero (M : Machine) (input : Bitstring) :
    eval M 0 input = none := rfl

@[simp] theorem runtime_zero (M : Machine) (input : Bitstring) :
    runtime M 0 input = none := rfl

end AvgCaseMls.Foundation
