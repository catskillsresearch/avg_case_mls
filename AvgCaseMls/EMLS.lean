/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.MLS

/-!
Elementary Multilevel Syllogistic (EMLS) literals and translations into MLS.

Literals follow Ferro–Omodeo–Schwartz [FOS80] §3 (`3-540-10009-1_8.pdf` in this repo):
conjunctions of (* ) $x = y \diamond z$, ($\in$) $x \in y$, ($\notin$) $x \notin y$, ($\neq$) $x \neq y$,
with $\diamond \in \{\cup,\cap,\setminus\}$ and $x,y,z$ set variables.
-/

namespace MLS.EMLS

/-! ### Elementary literals (FOS80 §3) -/

inductive BinOp
  | union
  | inter
  | diff
  deriving DecidableEq, Repr

inductive Literal
  | eqOp    : Nat → Nat → Nat → BinOp → Literal  -- (* )  x = y ◇ z
  | eqEmpty : Nat → Literal                      --       x = ∅
  | mem     : Nat → Nat → Literal                -- (∈)   x ∈ y
  | notMem  : Nat → Nat → Literal                -- (∉)   x ∉ y
  | neq     : Nat → Nat → Literal                -- (≠)   x ≠ y
  deriving DecidableEq, Repr

abbrev Conjunct := List Literal

def binOpToTerm (op : BinOp) (y z : Nat) : Term :=
  match op with
  | .union => Term.union (Term.var y) (Term.var z)
  | .inter => Term.inter (Term.var y) (Term.var z)
  | .diff  => Term.diff (Term.var y) (Term.var z)

def literalToFormula : Literal → Formula
  | .eqOp x y z op => Formula.rel (Relation.eq (Term.var x) (binOpToTerm op y z))
  | .eqEmpty x     => Formula.rel (Relation.eq (Term.var x) Term.empty)
  | .mem x y       => Formula.rel (Relation.mem (Term.var x) (Term.var y))
  | .notMem x y    => Formula.rel (Relation.not_mem (Term.var x) (Term.var y))
  | .neq x y       => Formula.rel (Relation.neq (Term.var x) (Term.var y))

def conjunctToFormula : Conjunct → Option Formula
  | [] => none
  | l :: ls =>
      some (ls.foldl (fun acc lit => Formula.and acc (literalToFormula lit)) (literalToFormula l))

def memLiterals (c : Conjunct) : List (Nat × Nat) :=
  c.filterMap fun
    | .mem x y => some (x, y)
    | _ => none

def notMemLiterals (c : Conjunct) : List (Nat × Nat) :=
  c.filterMap fun
    | .notMem x y => some (x, y)
    | _ => none

def neqLiterals (c : Conjunct) : List (Nat × Nat) :=
  c.filterMap fun
    | .neq x y => some (x, y)
    | _ => none

end MLS.EMLS
