/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.EMLS
import AvgCaseMls.SAT
import Mathlib

/-!
# The constructive SAT-to-EMLS reduction

This file formalizes the construction in the proof of Theorem 5.2 of
TR1995-711.  A propositional variable has two set variables, one for its
positive literal and one for its negative literal.  Their intersection is
forced to be empty.  A clause is represented by a chain of fresh variables
computing the union of its literal sets, followed by membership of a
distinguished element in the root of that chain.

The paper writes the last link as `Sₙ = vₙ`.  Equality of two variables is not
an elementary literal in the `MLS.EMLS` syntax used by this development.
We therefore use the exact elementary specialization
`Sₙ = vₙ ∪ e`, together with `e = ∅`.  This is semantically equivalent, and
also handles singleton clauses uniformly.  Empty clauses are represented by
the foundation-false literal `y ∈ y`.

Variable numbers are split into disjoint classes.  In particular every
set-operation result introduced for a clause is a positive multiple of four,
and is explicitly indexed by the clause number and suffix number using
`Nat.pair`.
-/

namespace EMLSReduction

open MLS
open MLS.EMLS

abbrev Satisfies (env : Env) (c : Conjunct) : Prop :=
  ∀ lit ∈ c, Literal.holds env lit

def EMLSSatisfiable (c : Conjunct) : Prop :=
  ∃ env, Satisfies env c

def distinguishedVar : Nat := 0
def emptyVar : Nat := 3
def positiveVar (i : Nat) : Nat := 4 * i + 1
def negativeVar (i : Nat) : Nat := 4 * i + 2
def intersectionVar (i : Nat) : Nat := 4 * i + 7

private def literalEquiv : SAT.Literal ≃ Sum Nat Nat where
  toFun
    | .pos i => .inl i
    | .neg i => .inr i
  invFun
    | .inl i => .pos i
    | .inr i => .neg i
  left_inv l := by cases l <;> rfl
  right_inv l := by cases l <;> rfl

private local instance : Encodable SAT.Literal :=
  Encodable.ofEquiv (Sum Nat Nat) literalEquiv

/-- A fresh result variable for the nonempty suffix `c` of clause `k`. -/
def gadgetVar (k : Nat) (c : SAT.Clause) : Nat :=
  4 * (Nat.pair k (Encodable.encode c) + 1)

theorem gadgetVar_eq_iff {k k' : Nat} {c c' : SAT.Clause} :
    gadgetVar k c = gadgetVar k' c' ↔ k = k' ∧ c = c' := by
  constructor
  · intro h
    have hp :
        Nat.pair k (Encodable.encode c) = Nat.pair k' (Encodable.encode c') := by
      have hs : Nat.pair k (Encodable.encode c) + 1 =
          Nat.pair k' (Encodable.encode c') + 1 := by
        apply Nat.mul_left_cancel (by decide : 0 < 4)
        exact h
      omega
    obtain ⟨hk, hc⟩ := Nat.pair_eq_pair.mp hp
    exact ⟨hk, Encodable.encode_injective hc⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem gadgetVar_ne_positive (k : Nat) (c : SAT.Clause) (i : Nat) :
    gadgetVar k c ≠ positiveVar i := by
  intro h
  have := congrArg (fun n => n % 4) h
  simp [gadgetVar, positiveVar] at this

theorem gadgetVar_ne_negative (k : Nat) (c : SAT.Clause) (i : Nat) :
    gadgetVar k c ≠ negativeVar i := by
  intro h
  have := congrArg (fun n => n % 4) h
  simp [gadgetVar, negativeVar] at this

theorem gadgetVar_ne_intersection (k : Nat) (c : SAT.Clause) (i : Nat) :
    gadgetVar k c ≠ intersectionVar i := by
  intro h
  have := congrArg (fun n => n % 4) h
  simp [gadgetVar, intersectionVar] at this

def literalVar : SAT.Literal → Nat
  | .pos i => positiveVar i
  | .neg i => negativeVar i

/-- The two elementary literals enforcing disjoint complementary truth sets. -/
def complementGadget (i : Nat) : Conjunct :=
  [ .eqOp (intersectionVar i) (positiveVar i) (negativeVar i) .inter
  , .eqEmpty (intersectionVar i)
  ]

def literalComplementGadget : SAT.Literal → Conjunct
  | .pos i => complementGadget i
  | .neg i => complementGadget i

/--
Set-operation links computing the union of all literal variables in a
nonempty suffix.  The final link unions with the explicitly empty variable.
-/
def clauseGadgets (k : Nat) : SAT.Clause → Conjunct
  | [] => []
  | l :: [] =>
      [.eqOp (gadgetVar k [l]) (literalVar l) emptyVar .union]
  | l :: rest@(_ :: _) =>
      .eqOp (gadgetVar k (l :: rest)) (literalVar l) (gadgetVar k rest) .union ::
        clauseGadgets k rest

def clauseCore (k : Nat) : SAT.Clause → Conjunct
  | [] => [.mem distinguishedVar distinguishedVar]
  | c@(_ :: _) => clauseGadgets k c ++ [.mem distinguishedVar (gadgetVar k c)]

def clausesCoreFrom : Nat → SAT.CNF → Conjunct
  | _, [] => []
  | k, c :: φ => clauseCore k c ++ clausesCoreFrom (k + 1) φ

def complementCore (φ : SAT.CNF) : Conjunct :=
  φ.flatMap fun c => c.flatMap literalComplementGadget

/-- The semantic core of the paper reduction. -/
def semanticCore (φ : SAT.CNF) : Conjunct :=
  .eqEmpty emptyVar :: (complementCore φ ++ clausesCoreFrom 0 φ)

private def boolSet (P : Prop) [Decidable P] : MLS.ZFSet :=
  if P then ({MLS.ZFSet.empty} : MLS.ZFSet) else MLS.ZFSet.empty

private theorem mem_boolSet (P : Prop) [Decidable P] :
    MLS.ZFSet.mem MLS.ZFSet.empty (boolSet P) ↔ P := by
  by_cases h : P <;> simp [boolSet, h, MLS.ZFSet.mem, MLS.ZFSet.empty]

private theorem boolSet_or (P Q : Prop) [Decidable P] [Decidable Q] [Decidable (P ∨ Q)] :
    boolSet (P ∨ Q) = MLS.ZFSet.union (boolSet P) (boolSet Q) := by
  ext x
  by_cases hp : P <;> by_cases hq : Q <;>
    simp [boolSet, hp, hq, MLS.ZFSet.union, MLS.ZFSet.empty]

private theorem boolSet_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    boolSet P = boolSet Q := by
  by_cases hp : P
  · simp [boolSet, hp, h.mp hp]
  · have hq : ¬Q := fun hQ => hp (h.mpr hQ)
    simp [boolSet, hp, hq]

private theorem boolSet_irrel (P : Prop) (d₁ d₂ : Decidable P) :
    @boolSet P d₁ = @boolSet P d₂ := by
  congr

/-- Canonical set model associated with a Boolean assignment. -/
noncomputable def model (a : SAT.Assignment) : Env := fun n =>
  if n = distinguishedVar then MLS.ZFSet.empty
  else
    match n % 4 with
    | 1 => @boolSet (a ((n - 1) / 4)) (Classical.propDecidable _)
    | 2 => @boolSet (¬a ((n - 2) / 4)) (Classical.propDecidable _)
    | 3 => MLS.ZFSet.empty
    | _ =>
        let kc := Nat.unpair (n / 4 - 1)
        @boolSet (SAT.evalClause a ((Encodable.decode kc.2).getD []))
          (Classical.propDecidable _)

@[simp] theorem model_distinguished (a : SAT.Assignment) :
    model a distinguishedVar = MLS.ZFSet.empty := by
  simp [model, distinguishedVar]

@[simp] theorem model_empty (a : SAT.Assignment) :
    model a emptyVar = MLS.ZFSet.empty := by
  simp [model, distinguishedVar, emptyVar]

@[simp] theorem model_positive (a : SAT.Assignment) (i : Nat) :
    model a (positiveVar i) =
      @boolSet (a i) (Classical.propDecidable _) := by
  classical
  have hdiv : 4 * i / 4 = i := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_left i (n := 4) (by decide)
  simp [model, distinguishedVar, positiveVar, hdiv]

@[simp] theorem model_negative (a : SAT.Assignment) (i : Nat) :
    model a (negativeVar i) =
      @boolSet (¬a i) (Classical.propDecidable _) := by
  classical
  simp [model, distinguishedVar, negativeVar]
  apply boolSet_irrel

@[simp] theorem model_intersection (a : SAT.Assignment) (i : Nat) :
    model a (intersectionVar i) = MLS.ZFSet.empty := by
  simp [model, distinguishedVar, intersectionVar]

@[simp] theorem model_gadget (a : SAT.Assignment) (k : Nat) (c : SAT.Clause) :
    model a (gadgetVar k c) =
      @boolSet (SAT.evalClause a c) (Classical.propDecidable _) := by
  classical
  have hdiv : 4 * (Nat.pair k (Encodable.encode c) + 1) / 4 =
      Nat.pair k (Encodable.encode c) + 1 :=
    by
      rw [Nat.mul_comm]
      exact Nat.mul_div_left _ (n := 4) (by decide)
  simp [model, distinguishedVar, gadgetVar, hdiv, Nat.unpair_pair, Encodable.encodek]

private theorem model_literalVar (a : SAT.Assignment) (l : SAT.Literal) :
    model a (literalVar l) =
      @boolSet (SAT.evalLiteral a l) (Classical.propDecidable _) := by
  classical
  cases l with
  | pos i =>
      simp only [literalVar, SAT.evalLiteral]
      exact model_positive a i
  | neg i =>
      simp only [literalVar, SAT.evalLiteral]
      calc
        model a (negativeVar i) =
            @boolSet (¬a i) (Classical.propDecidable _) := model_negative a i
        _ = @boolSet (¬a i) (Classical.propDecidable _) := rfl

private theorem clauseGadgets_model (a : SAT.Assignment)
    (k : Nat) (c : SAT.Clause) :
    Satisfies (model a) (clauseGadgets k c) := by
  classical
  induction c with
  | nil =>
      intro lit h
      simp [clauseGadgets] at h
  | cons l rest ih =>
      cases rest with
      | nil =>
          intro lit h
          simp only [clauseGadgets, List.mem_singleton] at h
          subst h
          simp only [Literal.holds, binOpToTerm, evalTerm, model_gadget,
            model_literalVar, model_empty]
          rw [boolSet_congr (SAT.evalClause_cons a l [])]
          simp only [SAT.evalClause_nil, or_false]
          simpa [boolSet] using boolSet_or (SAT.evalLiteral a l) False
      | cons l' rest =>
          intro lit h
          simp only [clauseGadgets, List.mem_cons] at h
          rcases h with rfl | h
          · simp only [Literal.holds, binOpToTerm, evalTerm, model_gadget,
              model_literalVar]
            rw [boolSet_congr (SAT.evalClause_cons a l (l' :: rest))]
            exact boolSet_or (SAT.evalLiteral a l) (SAT.evalClause a (l' :: rest))
          · exact ih lit h

private theorem complementGadget_model (a : SAT.Assignment) (i : Nat) :
    Satisfies (model a) (complementGadget i) := by
  by_cases h : a i <;>
    simp [complementGadget, Satisfies, Literal.holds, binOpToTerm, evalTerm,
      boolSet, h, MLS.ZFSet.inter, MLS.ZFSet.empty]

private theorem complementCore_model (φ : SAT.CNF) (a : SAT.Assignment) :
    Satisfies (model a) (complementCore φ) := by
  intro lit hlit
  change lit ∈ φ.flatMap (fun c => c.flatMap fun l =>
    literalComplementGadget l) at hlit
  obtain ⟨c, hc, hlit⟩ := List.mem_flatMap.mp hlit
  obtain ⟨l, hl, hlit⟩ := List.mem_flatMap.mp hlit
  cases l <;> exact complementGadget_model a _ lit hlit

private theorem clauseCore_model (a : SAT.Assignment)
    (k : Nat) (c : SAT.Clause)
    (hc : SAT.evalClause a c) :
    Satisfies (model a) (clauseCore k c) := by
  cases c with
  | nil => simp [SAT.evalClause] at hc
  | cons l rest =>
      intro lit hlit
      simp only [clauseCore, List.mem_append, List.mem_singleton] at hlit
      cases hlit with
      | inl h =>
          exact clauseGadgets_model a k (l :: rest) lit h
      | inr h =>
          subst h
          simp [Literal.holds, evalTerm, model_gadget, mem_boolSet, hc]

private theorem clausesCoreFrom_model (φ : SAT.CNF) (a : SAT.Assignment) (k : Nat)
    (ha : SAT.evalCNF a φ) :
    Satisfies (model a) (clausesCoreFrom k φ) := by
  induction φ generalizing k with
  | nil =>
      intro lit h
      simp [clausesCoreFrom] at h
  | cons c cs ih =>
      intro lit hlit
      simp only [clausesCoreFrom, List.mem_append] at hlit
      cases hlit with
      | inl h =>
          exact clauseCore_model a k c (ha c (by simp)) lit h
      | inr h =>
          apply ih (k + 1)
          · intro d hd
            exact ha d (by simp [hd])
          · exact h

theorem satisfiable_imp (φ : SAT.CNF) :
    SAT.Satisfiable φ → EMLSSatisfiable (semanticCore φ) := by
  rintro ⟨a, ha⟩
  refine ⟨model a, ?_⟩
  intro lit hlit
  simp only [semanticCore, List.mem_cons, List.mem_append] at hlit
  rcases hlit with rfl | h | h
  · simp [Literal.holds, evalTerm]
  · exact complementCore_model φ a lit h
  · exact clausesCoreFrom_model φ a 0 ha lit h

private def assignmentOfModel (env : Env) : SAT.Assignment := fun i =>
  ZFSet.mem (env distinguishedVar) (env (positiveVar i))

private def rawLiteral (env : Env) (l : SAT.Literal) : Prop :=
  ZFSet.mem (env distinguishedVar) (env (literalVar l))

private theorem clauseGadgets_raw (env : Env) (hempty : env emptyVar = ZFSet.empty)
    (k : Nat) (c : SAT.Clause) (hne : c ≠ [])
    (hg : Satisfies env (clauseGadgets k c))
    (hroot : ZFSet.mem (env distinguishedVar) (env (gadgetVar k c))) :
    ∃ l ∈ c, rawLiteral env l := by
  induction c with
  | nil => contradiction
  | cons l rest ih =>
      cases rest with
      | nil =>
          refine ⟨l, by simp, ?_⟩
          have heq := hg
            (.eqOp (gadgetVar k [l]) (literalVar l) emptyVar .union) (by
              simp [clauseGadgets])
          simp only [Literal.holds, binOpToTerm, evalTerm] at heq
          rw [heq, hempty] at hroot
          change env distinguishedVar ∈ env (literalVar l) ∪ MLS.ZFSet.empty at hroot
          rcases (_root_.ZFSet.mem_union.mp hroot) with hl | hf
          · exact hl
          · exact False.elim ((_root_.ZFSet.notMem_empty _) hf)
      | cons l' rest =>
          have heq := hg
            (.eqOp (gadgetVar k (l :: l' :: rest)) (literalVar l)
              (gadgetVar k (l' :: rest)) .union) (by simp [clauseGadgets])
          simp only [Literal.holds, binOpToTerm, evalTerm] at heq
          rw [heq] at hroot
          change env distinguishedVar ∈
            env (literalVar l) ∪ env (gadgetVar k (l' :: rest)) at hroot
          rw [_root_.ZFSet.mem_union] at hroot
          cases hroot with
          | inl hl => exact ⟨l, by simp, hl⟩
          | inr hr =>
              obtain ⟨w, hw, hraw⟩ := ih
                (by simp)
                (fun lit hlit => hg lit (by simp [clauseGadgets, hlit]))
                hr
              exact ⟨w, by simp [hw], hraw⟩

private theorem complement_for_literal {φ : SAT.CNF} {c : SAT.Clause}
    (hc : c ∈ φ) {l : SAT.Literal} (hl : l ∈ c) :
    ∀ lit ∈ (match l with
      | .pos i => complementGadget i
      | .neg i => complementGadget i),
      lit ∈ complementCore φ := by
  intro lit hlit
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨l, hl, hlit⟩

private theorem negative_sound (env : Env) (i : Nat)
    (hg : Satisfies env (complementGadget i))
    (hn : ZFSet.mem (env distinguishedVar) (env (negativeVar i))) :
    ¬assignmentOfModel env i := by
  intro hp
  have hop := hg
    (.eqOp (intersectionVar i) (positiveVar i) (negativeVar i) .inter) (by
      simp [complementGadget])
  have hemp := hg (.eqEmpty (intersectionVar i)) (by simp [complementGadget])
  simp only [Literal.holds, binOpToTerm, evalTerm] at hop hemp
  have hi : env distinguishedVar ∈
      env (positiveVar i) ∩ env (negativeVar i) := by
    apply _root_.ZFSet.mem_inter.mpr
    exact ⟨hp, hn⟩
  change env (intersectionVar i) = env (positiveVar i) ∩ env (negativeVar i) at hop
  rw [← hop, hemp] at hi
  exact (_root_.ZFSet.notMem_empty _) hi

private theorem clauseCore_sound (φ : SAT.CNF) (env : Env)
    (hempty : env emptyVar = ZFSet.empty)
    (hcomp : Satisfies env (complementCore φ))
    (k : Nat) (c : SAT.Clause) (hc : c ∈ φ)
    (hcore : Satisfies env (clauseCore k c)) :
    SAT.evalClause (assignmentOfModel env) c := by
  cases c with
  | nil =>
      have hself := hcore (.mem distinguishedVar distinguishedVar) (by
        simp [clauseCore])
      exact False.elim (EMLS.step4_self_loop_unsat env distinguishedVar hself)
  | cons l rest =>
      have hg : Satisfies env (clauseGadgets k (l :: rest)) := fun lit hlit =>
        hcore lit (by simp [clauseCore, hlit])
      have hm := hcore (.mem distinguishedVar (gadgetVar k (l :: rest))) (by
        simp [clauseCore])
      simp only [Literal.holds, evalTerm] at hm
      obtain ⟨w, hw, hraw⟩ :=
        clauseGadgets_raw env hempty k (l :: rest) (by simp) hg hm
      refine ⟨w, hw, ?_⟩
      cases w with
      | pos i => exact hraw
      | neg i =>
          simp only [SAT.evalLiteral]
          apply negative_sound env i
          · intro lit hlit
            apply hcomp lit
            exact complement_for_literal hc hw lit hlit
          · exact hraw

private theorem clausesCoreFrom_sound (φ : SAT.CNF) (env : Env)
    (hempty : env emptyVar = ZFSet.empty)
    (hcomp : Satisfies env (complementCore φ))
    (k : Nat) (cs : SAT.CNF) (hsub : ∀ c ∈ cs, c ∈ φ)
    (hcore : Satisfies env (clausesCoreFrom k cs)) :
    SAT.evalCNF (assignmentOfModel env) cs := by
  induction cs generalizing k with
  | nil => simp [SAT.evalCNF]
  | cons c cs ih =>
      rw [SAT.evalCNF_cons]
      constructor
      · apply clauseCore_sound φ env hempty hcomp k c (hsub c (by simp))
        intro lit hlit
        apply hcore lit
        simp [clausesCoreFrom, hlit]
      · apply ih (k + 1)
        · intro d hd
          exact hsub d (by simp [hd])
        · intro lit hlit
          apply hcore lit
          simp [clausesCoreFrom, hlit]

theorem imp_satisfiable (φ : SAT.CNF) :
    EMLSSatisfiable (semanticCore φ) → SAT.Satisfiable φ := by
  rintro ⟨env, henv⟩
  have hemptyLit := henv (.eqEmpty emptyVar) (by simp [semanticCore])
  simp only [Literal.holds, evalTerm] at hemptyLit
  have hcomp : Satisfies env (complementCore φ) := by
    intro lit hlit
    exact henv lit (by simp [semanticCore, hlit])
  have hclauses : Satisfies env (clausesCoreFrom 0 φ) := by
    intro lit hlit
    exact henv lit (by simp [semanticCore, hlit])
  refine ⟨assignmentOfModel env, ?_⟩
  exact clausesCoreFrom_sound φ env hemptyLit hcomp 0 φ
    (fun c hc => hc) hclauses

/-- Exact semantic correctness of the constructive Theorem 5.2 reduction. -/
theorem satisfiable_iff (φ : SAT.CNF) :
    SAT.Satisfiable φ ↔ EMLSSatisfiable (semanticCore φ) :=
  ⟨satisfiable_imp φ, imp_satisfiable φ⟩

/-! ## Honest syntactic packaging and inversion

The semantic core is prefixed by one idempotence literal carrying the standard
computable encoding of the source CNF.  This literal is valid in every model
(`t = t ∪ t`) and therefore does not alter the paper construction.  It makes
the promised injectivity and computable left inverse explicit.  The node-count
bounds below count each natural-number variable index as one syntax node, as
the other structural metrics in this development do; they do not claim a
bit-cost bound for `Encodable.encode`.
-/

def provenanceTag (φ : SAT.CNF) : Literal :=
  let n := Encodable.encode φ
  .eqOp n n n .union

/-- The injective, syntactically invertible EMLS reduction. -/
def toEMLS (φ : SAT.CNF) : Conjunct :=
  provenanceTag φ :: semanticCore φ

def fromEMLS : Conjunct → Option SAT.CNF
  | .eqOp x y z .union :: _ =>
      if x = y ∧ y = z then Encodable.decode x else none
  | _ => none

@[simp] theorem fromEMLS_toEMLS (φ : SAT.CNF) :
    fromEMLS (toEMLS φ) = some φ := by
  simp [fromEMLS, toEMLS, provenanceTag, Encodable.encodek]

theorem toEMLS_injective : Function.Injective toEMLS := by
  intro φ ψ h
  have := congrArg fromEMLS h
  simpa using this

private theorem provenanceTag_holds (env : Env) (φ : SAT.CNF) :
    Literal.holds env (provenanceTag φ) := by
  simp only [provenanceTag, Literal.holds, binOpToTerm, evalTerm]
  apply _root_.ZFSet.ext
  intro x
  change (x ∈ env (Encodable.encode φ)) ↔
    x ∈ env (Encodable.encode φ) ∪ env (Encodable.encode φ)
  rw [_root_.ZFSet.mem_union]
  tauto

theorem toEMLS_satisfiable_iff (φ : SAT.CNF) :
    SAT.Satisfiable φ ↔ EMLSSatisfiable (toEMLS φ) := by
  rw [satisfiable_iff]
  constructor
  · rintro ⟨env, henv⟩
    refine ⟨env, ?_⟩
    intro lit hlit
    simp only [toEMLS, List.mem_cons] at hlit
    rcases hlit with rfl | hlit
    · exact provenanceTag_holds env φ
    · exact henv lit hlit
  · rintro ⟨env, henv⟩
    exact ⟨env, fun lit hlit => henv lit (by simp [toEMLS, hlit])⟩

/-! ## Exact structural and linear bounds -/

def literalCount (φ : SAT.CNF) : Nat :=
  (φ.map List.length).sum

private theorem complementList_length (c : SAT.Clause) :
    (c.flatMap literalComplementGadget).length = 2 * c.length := by
  induction c with
  | nil => simp
  | cons l c ih =>
      cases l <;> simp [literalComplementGadget, complementGadget, ih] <;> omega

private theorem complementCore_length (φ : SAT.CNF) :
    (complementCore φ).length = 2 * literalCount φ := by
  induction φ with
  | nil => simp [complementCore, literalCount]
  | cons c φ ih =>
      simp only [complementCore, List.flatMap_cons, List.length_append,
        literalCount, List.map_cons, List.sum_cons]
      rw [complementList_length]
      change 2 * c.length + (complementCore φ).length =
        2 * (c.length + literalCount φ)
      rw [ih]
      omega

private theorem clauseGadgets_length (k : Nat) (c : SAT.Clause) :
    (clauseGadgets k c).length = c.length := by
  induction c with
  | nil => simp [clauseGadgets]
  | cons l c ih =>
      cases c <;> simp [clauseGadgets, ih]

private theorem clauseCore_length (k : Nat) (c : SAT.Clause) :
    (clauseCore k c).length = c.length + 1 := by
  cases c with
  | nil => simp [clauseCore]
  | cons l c =>
      simp [clauseCore, clauseGadgets_length]

private theorem clausesCoreFrom_length (k : Nat) (φ : SAT.CNF) :
    (clausesCoreFrom k φ).length = literalCount φ + φ.length := by
  induction φ generalizing k with
  | nil => simp [clausesCoreFrom, literalCount]
  | cons c φ ih =>
      simp [clausesCoreFrom, clauseCore_length, literalCount, ih]
      omega

theorem semanticCore_length (φ : SAT.CNF) :
    (semanticCore φ).length = 1 + 3 * literalCount φ + φ.length := by
  simp [semanticCore, complementCore_length, clausesCoreFrom_length]
  omega

/-- Exact output length of the tagged constructive reduction. -/
theorem toEMLS_length (φ : SAT.CNF) :
    (toEMLS φ).length = 2 + 3 * literalCount φ + φ.length := by
  simp [toEMLS, semanticCore_length]
  omega

/-- The EMLS conjunct has at most three literals per SAT structural unit. -/
theorem toEMLS_length_le (φ : SAT.CNF) :
    (toEMLS φ).length ≤ 3 * SAT.size φ := by
  rw [toEMLS_length]
  simp [SAT.size, literalCount]
  omega

end EMLSReduction
