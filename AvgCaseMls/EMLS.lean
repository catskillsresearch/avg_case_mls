/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.MLS

/-!
**Phase 2B complete:** `Literal`, `literalToFormula`, `conjunctToFormula`, `Literal.holds`, translation lemmas; `relationToLiteral?` for §7 normalization.

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
  | [l] => some (literalToFormula l)
  | l :: ls@(_ :: _) =>
      match conjunctToFormula ls with
      | none => none
      | some f => some (Formula.and (literalToFormula l) f)

/-! ### Semantics and translation lemmas (Phase 2B) -/

/-- Semantic satisfaction of an elementary literal under `env`. -/
noncomputable def Literal.holds (env : Env) : Literal → Prop
  | .eqOp x y z op =>
      evalTerm env (Term.var x) = evalTerm env (binOpToTerm op y z)
  | .eqEmpty x =>
      evalTerm env (Term.var x) = evalTerm env Term.empty
  | .mem x y =>
      ZFSet.mem (evalTerm env (Term.var x)) (evalTerm env (Term.var y))
  | .notMem x y =>
      ¬ ZFSet.mem (evalTerm env (Term.var x)) (evalTerm env (Term.var y))
  | .neq x y =>
      evalTerm env (Term.var x) ≠ evalTerm env (Term.var y)

theorem literalToFormula_eval (env : Env) (lit : Literal) :
    evalFormula env (literalToFormula lit) ↔ Literal.holds env lit := by
  cases lit <;> simp [Literal.holds, literalToFormula, evalFormula, evalTerm, binOpToTerm]

private theorem conjunctToFormula_some_of_ne_nil {c : Conjunct} (h : c ≠ []) :
    ∃ f, conjunctToFormula c = some f := by
  cases c with
  | nil => contradiction
  | cons l ls =>
    cases ls with
    | nil => exact ⟨literalToFormula l, by simp [conjunctToFormula]⟩
    | cons l' ls' =>
      obtain ⟨f, hf⟩ := @conjunctToFormula_some_of_ne_nil (l' :: ls') (List.cons_ne_nil l' ls')
      exact ⟨Formula.and (literalToFormula l) f, by simp [conjunctToFormula, hf]⟩

theorem conjunctToFormula_none_iff (c : Conjunct) :
    conjunctToFormula c = none ↔ c = [] := by
  constructor
  · intro h
    cases c with
    | nil => rfl
    | cons l ls =>
      obtain ⟨f, hf⟩ := @conjunctToFormula_some_of_ne_nil (l :: ls) (List.cons_ne_nil l ls)
      rw [hf] at h
      cases h
  · intro h; subst h; simp [conjunctToFormula]

theorem conjunctToFormula_singleton (lit : Literal) :
    conjunctToFormula [lit] = some (literalToFormula lit) := by
  simp [conjunctToFormula]

theorem conjunctToFormula_eval (env : Env) (c : Conjunct) (f : Formula)
    (h : conjunctToFormula c = some f) :
    evalFormula env f ↔ ∀ lit ∈ c, Literal.holds env lit := by
  induction c generalizing f with
  | nil => simp [conjunctToFormula] at h
  | cons l ls ih =>
      cases ls with
      | nil =>
          simp [conjunctToFormula] at h
          subst h
          simp [literalToFormula_eval]
      | cons l' ls' =>
          simp [conjunctToFormula] at h
          cases h' : conjunctToFormula (l' :: ls') with
          | none =>
            exfalso
            have := @conjunctToFormula_some_of_ne_nil (l' :: ls') (List.cons_ne_nil l' ls')
            simp [h'] at this
          | some f' =>
            rw [h'] at h
            injection h with hf_eq
            subst hf_eq
            have ih' := ih f' h'
            simp only [literalToFormula_eval, List.mem_cons, evalFormula, ih']
            constructor
            · intro ⟨h0, h1⟩ lit hl
              cases hl with
              | inl hl => subst hl; exact h0
              | inr hl => exact h1 lit hl
            · intro hall
              exact ⟨hall l (by simp), fun lit hl => hall lit (Or.inr hl)⟩

/-! ### MLS relation ↔ literal (FOS80 §3 patterns) -/

def varTerm? : Term → Option Nat
  | Term.var n => some n
  | _ => none

def binaryOpTerm? : Term → Option (Nat × Nat × BinOp)
  | Term.union (Term.var y) (Term.var z) => some (y, z, .union)
  | Term.inter (Term.var y) (Term.var z) => some (y, z, .inter)
  | Term.diff (Term.var y) (Term.var z) => some (y, z, .diff)
  | _ => none

def relationToLiteral? : Relation → Option Literal
  | Relation.mem t1 t2 => do
      let x ← varTerm? t1
      let y ← varTerm? t2
      return .mem x y
  | Relation.not_mem t1 t2 => do
      let x ← varTerm? t1
      let y ← varTerm? t2
      return .notMem x y
  | Relation.eq t1 Term.empty => do
      let x ← varTerm? t1
      return .eqEmpty x
  | Relation.eq (Term.var x) t2 => do
      let (y, z, op) ← binaryOpTerm? t2
      return .eqOp x y z op
  | Relation.neq t1 t2 => do
      let x ← varTerm? t1
      let y ← varTerm? t2
      return .neq x y
  | _ => none

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
