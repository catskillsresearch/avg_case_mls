/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.EMLS

/-!
Decision procedure skeleton for MLS / EMLS satisfiability.

Algorithm structure from Ferro–Omodeo–Schwartz [FOS80] §3 (`3-540-10009-1_8.pdf`):
1. Normalize to a conjunction of elementary literals (partial: `formulaToConjunct?`).
2. Step 2 — detect immediate contradictions ($x \neq x$, $x \in y \land x \notin y$, …).
3. Step 3 — if no membership literals remain, report SATISFIABLE.
4. Step 4 — singleton-model search via membership-order cycle detection (partial).

Full Step 1 substitution and complete Step 4 are still open (Phase 2C).
Soundness / completeness theorems use **satisfiability**, not validity.
-/

namespace MLS

open EMLS

/-! ### Formula → EMLS conjunct (partial normalization) -/

def formulaToConjunct? : Formula → Option Conjunct
  | Formula.rel r =>
      EMLS.relationToLiteral? r |>.map List.singleton
  | Formula.and f1 f2 => do
      let c1 ← formulaToConjunct? f1
      let c2 ← formulaToConjunct? f2
      return c1 ++ c2
  | _ => none

/-! ### FOS80 Step 2: immediate contradictions -/

def hasStep2Contradiction (c : Conjunct) : Bool :=
  c.any fun lit1 =>
    c.any fun lit2 =>
      match lit1, lit2 with
      | .neq x y, _ => x = y
      | .mem x y, .notMem x' y' => x = x' && y = y'
      | _, _ => false

/-! ### FOS80 Step 3: no membership constraints -/

def hasMembershipLiteral (c : Conjunct) : Bool :=
  c.any fun
    | .mem _ _ | .notMem _ _ => true
    | _ => false

/-! ### FOS80 Step 4 (partial): cycle in membership order -/

def varsInConjunct (c : Conjunct) : List Nat :=
  (c.flatMap fun
    | .eqOp x y z _ => [x, y, z]
    | .eqEmpty x => [x]
    | .mem x y | .notMem x y | .neq x y => [x, y]).eraseDups

def hasMemCycle (edges : List (Nat × Nat)) (nodes : List Nat) : Bool :=
  let fuel := nodes.length + 1
  let rec dfs (remaining : Nat) (path : List Nat) (u : Nat) : Bool :=
    if remaining = 0 then
      false
    else if path.contains u then
      true
    else
      let path' := u :: path
      (edges.filterMap fun (a, b) => if a = u then some b else none).any (dfs (remaining - 1) path')
  nodes.any fun start => dfs fuel [] start

def hasStep4Obstruction (c : Conjunct) : Bool :=
  let mem := memLiterals c
  let notMem := notMemLiterals c
  let nodes := varsInConjunct c
  hasMemCycle mem nodes ||
  (notMem.any fun (x, y) => x = y && mem.contains (x, y))

def decideConjunct (c : Conjunct) : Bool :=
  if hasStep2Contradiction c then false
  else if !hasMembershipLiteral c then true
  else if hasStep4Obstruction c then false
  else true

/-- EMLS conjunct satisfiability (FOS80 Steps 2–4; Phase 2C proofs open). -/
def decideEMLSSat (c : Conjunct) : Bool :=
  decideConjunct c

/-! ### Top-level MLS satisfiability checker -/

def decideMLSSat (f : Formula) : Bool :=
  match formulaToConjunct? f with
  | some c => decideConjunct c
  | none =>
      match f with
      | Formula.rel (Relation.eq Term.empty Term.empty) => true
      | Formula.rel (Relation.neq Term.empty Term.empty) => false
      | _ => false

/-- If `c` translates to a formula, `decideEMLSSat?` runs `decideMLSSat` on it. -/
def decideEMLSSat? (c : Conjunct) : Option Bool :=
  conjunctToFormula c |>.map decideMLSSat

/-- Legacy name kept for tests and arxiv listings. -/
abbrev decideMLS := decideMLSSat

/-! ### Soundness / completeness (Phase 2C — proofs open) -/

theorem decideMLSSat_sound (f : Formula) (h : decideMLSSat f = true) :
    ∃ (env : Env), evalFormula env f := by
  sorry

theorem decideMLSSat_complete (f : Formula) (h : ∃ (env : Env), evalFormula env f) :
    decideMLSSat f = true := by
  sorry

theorem decideMLS_sound (f : Formula) (h : decideMLS f = true) :
    ∃ (env : Env), evalFormula env f :=
  decideMLSSat_sound f h

theorem decideMLS_complete (f : Formula) (h : ∃ (env : Env), evalFormula env f) :
    decideMLS f = true :=
  decideMLSSat_complete f h

end MLS
