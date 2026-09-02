/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import Mathlib

/-!
# Finite propositional clauses and resolution

This is the syntax used in Chvátal--Szemerédi and TR1995: variables are
`Fin n`, clauses are sets, and an ordinary clause contains exactly one signed
literal over each of `k` distinct variables.
-/

namespace AvgCaseMls.Section3

abbrev Literal (n : Nat) := Fin n × Bool

namespace Literal

def pos (x : Fin n) : Literal n := (x, true)

def neg (x : Fin n) : Literal n := (x, false)

def varOf (l : Literal n) : Fin n := l.1

def complement (l : Literal n) : Literal n := (l.1, !l.2)

@[simp] theorem complement_complement (l : Literal n) :
    l.complement.complement = l := by
  rcases l with ⟨x, b⟩
  simp [complement]

@[simp] theorem varOf_complement (l : Literal n) :
    l.complement.varOf = l.varOf := rfl

@[simp] theorem complement_ne (l : Literal n) : l.complement ≠ l := by
  rcases l with ⟨x, b⟩
  simp [complement]

end Literal

abbrev Clause (n : Nat) := Finset (Literal n)
abbrev CNF (n m : Nat) := Fin m → Clause n
abbrev Assignment (n : Nat) := Fin n → Bool

def evalLiteral (a : Assignment n) (l : Literal n) : Bool :=
  if l.2 then a l.1 else !(a l.1)

def SatisfiesClause (a : Assignment n) (C : Clause n) : Prop :=
  ∃ l ∈ C, evalLiteral a l = true

def SatisfiesCNF (a : Assignment n) (F : Fin m → Clause n) : Prop :=
  ∀ i, SatisfiesClause a (F i)

def Satisfiable (F : Fin m → Clause n) : Prop :=
  ∃ a, SatisfiesCNF a F

@[simp] theorem evalLiteral_complement (a : Assignment n) (l : Literal n) :
    evalLiteral a l.complement = !(evalLiteral a l) := by
  rcases l with ⟨x, b⟩
  cases b <;> simp [evalLiteral, Literal.complement]

@[simp] theorem not_satisfies_empty (a : Assignment n) :
    ¬ SatisfiesClause a (∅ : Clause n) := by simp [SatisfiesClause]

/-- A `k`-clause with distinct variables; this also excludes complementary pairs. -/
def IsOrdinary (k : Nat) (C : Clause n) : Prop :=
  C.card = k ∧
    ∀ ⦃l₁⦄, l₁ ∈ C → ∀ ⦃l₂⦄, l₂ ∈ C →
      l₁.varOf = l₂.varOf → l₁ = l₂

abbrev ClauseVariables (n k : Nat) := {S : Finset (Fin n) // S.card = k}

noncomputable instance : Fintype (ClauseVariables n k) := Fintype.ofFinite _

/-- An exact-size variable set together with one sign for every selected variable. -/
abbrev OrdinaryClause (n k : Nat) :=
  Sigma fun S : ClauseVariables n k => ((x : S.val) → Bool)

namespace OrdinaryClause

def varSet (C : OrdinaryClause n k) : Finset (Fin n) := C.1.val

def lits (C : OrdinaryClause n k) : Clause n :=
  C.1.val.attach.image fun x => (x.val, C.2 x)

@[simp] theorem varSet_card (C : OrdinaryClause n k) :
    C.varSet.card = k := C.1.property

@[simp] theorem lits_card (C : OrdinaryClause n k) : C.lits.card = k := by
  rw [lits, Finset.card_image_iff.mpr]
  · simpa [varSet] using C.1.property
  intro x _ y _ h
  exact Subtype.ext (congrArg Prod.fst h)

theorem lits_variable_injective (C : OrdinaryClause n k)
    ⦃l₁⦄ (h₁ : l₁ ∈ C.lits) ⦃l₂⦄ (h₂ : l₂ ∈ C.lits)
    (hvar : l₁.varOf = l₂.varOf) : l₁ = l₂ := by
  simp only [lits, Finset.mem_image] at h₁ h₂
  rcases h₁ with ⟨x, _, rfl⟩
  rcases h₂ with ⟨y, _, rfl⟩
  have hxy : x = y := Subtype.ext hvar
  subst y
  rfl

theorem lits_isOrdinary (C : OrdinaryClause n k) : IsOrdinary k C.lits :=
  ⟨C.lits_card, fun _ h₁ _ h₂ => C.lits_variable_injective h₁ h₂⟩

theorem complement_not_mem (C : OrdinaryClause n k) {l : Literal n}
    (hl : l ∈ C.lits) : l.complement ∉ C.lits := by
  intro hc
  have := C.lits_variable_injective hc hl (by simp)
  exact Literal.complement_ne l this

theorem mem_varSet_iff (C : OrdinaryClause n k) (x : Fin n) :
    x ∈ C.varSet ↔ ∃ l ∈ C.lits, l.varOf = x := by
  constructor
  · intro hx
    change x ∈ C.1.val at hx
    let sx : C.1.val := ⟨x, hx⟩
    refine ⟨(x, C.2 sx), ?_, rfl⟩
    simp only [lits, Finset.mem_image]
    exact ⟨sx, Finset.mem_attach _ sx, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    simp only [lits, Finset.mem_image] at hl
    rcases hl with ⟨y, _, hy⟩
    change l.1 ∈ C.1.val
    simp [← hy, y.property]

end OrdinaryClause

private noncomputable def clauseVariablesEquivPowerset :
    ClauseVariables n k ≃ {S // S ∈ (Finset.univ : Finset (Fin n)).powersetCard k} where
  toFun S := ⟨S.val, by simp [S.property]⟩
  invFun S := ⟨S.val, by simpa using (Finset.mem_powersetCard.mp S.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem clauseVariables_card :
    Fintype.card (ClauseVariables n k) = n.choose k := by
  rw [Fintype.card_congr clauseVariablesEquivPowerset, Fintype.card_coe,
    Finset.card_powersetCard]
  simp

theorem ordinaryClause_cardinality :
    Fintype.card (OrdinaryClause n k) = n.choose k * 2 ^ k := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  have hterm :
      (fun S : ClauseVariables n k => 2 ^ S.val.card) = fun _ => 2 ^ k := by
    funext S
    rw [S.property]
  rw [hterm, Finset.sum_const, Finset.card_univ, clauseVariables_card]
  exact nsmul_eq_mul _ _

/-- The finite space of all ordinary `k`-clauses on `n` named variables. -/
noncomputable def ordinaryClauseSpace (n k : Nat) : Finset (OrdinaryClause n k) :=
  Finset.univ

@[simp] theorem mem_ordinaryClauseSpace (C : OrdinaryClause n k) :
    C ∈ ordinaryClauseSpace n k := Finset.mem_univ C

theorem ordinaryClauseSpace_finite :
    Set.Finite (Set.univ : Set (OrdinaryClause n k)) := Set.toFinite _

@[simp] theorem ordinaryClauseSpace_card :
    (ordinaryClauseSpace n k).card = Fintype.card (OrdinaryClause n k) := by
  simp [ordinaryClauseSpace]

/-- The all-positive clause on the first `k` variables. -/
noncomputable def positiveOrdinaryClause (hk : k ≤ n) : OrdinaryClause n k := by
  let f : Fin k → Fin n := fun i => Fin.castLE hk i
  let S : ClauseVariables n k := ⟨Finset.univ.image f, by
    rw [Finset.card_image_iff.mpr]
    · simp
    intro i _ j _ hij
    exact Fin.ext (congrArg (fun z : Fin n => z.val) hij)⟩
  exact ⟨S, fun _ => true⟩

theorem ordinaryClause_nonempty (hk : k ≤ n) :
    Nonempty (OrdinaryClause n k) :=
  ⟨positiveOrdinaryClause hk⟩

/-- The resolvent used in CS87: no side conditions beyond the pivot occurrences. -/
def resolvent (A B : Clause n) (x : Fin n) : Clause n :=
  (A.erase (Literal.pos x)) ∪ (B.erase (Literal.neg x))

def IsResolvent (C A B : Clause n) : Prop :=
  ∃ x, Literal.pos x ∈ A ∧ Literal.neg x ∈ B ∧ C = resolvent A B x

theorem resolution_sound {a : Assignment n} {A B C : Clause n}
    (hA : SatisfiesClause a A) (hB : SatisfiesClause a B)
    (hC : IsResolvent C A B) : SatisfiesClause a C := by
  rcases hC with ⟨x, hxA, hxB, rfl⟩
  by_cases hax : a x = true
  · rcases hB with ⟨l, hl, heval⟩
    have hne : l ≠ Literal.neg x := by
      intro h
      subst l
      simp [evalLiteral, Literal.neg, hax] at heval
    exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hl⟩), heval⟩
  · rcases hA with ⟨l, hl, heval⟩
    have hne : l ≠ Literal.pos x := by
      intro h
      subst l
      simp [evalLiteral, Literal.pos, hax] at heval
    exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hl⟩), heval⟩

/-- A generated sequence; old clauses may be reused and repeated. -/
inductive ResolutionProof (F : Fin m → Clause n) : List (Clause n) → Prop
  | nil : ResolutionProof F []
  | input (cs : List (Clause n)) (h : ResolutionProof F cs) (i : Fin m) :
      ResolutionProof F (cs ++ [F i])
  | resolve (cs : List (Clause n)) (h : ResolutionProof F cs) (A B : Clause n)
      (hA : A ∈ cs) (hB : B ∈ cs) (C : Clause n) (hC : IsResolvent C A B) :
      ResolutionProof F (cs ++ [C])

def ResolutionRefutation (F : Fin m → Clause n) (cs : List (Clause n)) : Prop :=
  ResolutionProof F cs ∧ (∅ : Clause n) ∈ cs

theorem resolutionProof_sound {F : Fin m → Clause n} {cs : List (Clause n)}
    (hp : ResolutionProof F cs) {a : Assignment n} (ha : SatisfiesCNF a F) :
    ∀ C ∈ cs, SatisfiesClause a C := by
  induction hp with
  | nil => simp
  | input cs hp i ih =>
      intro C hC
      simp only [List.mem_append, List.mem_singleton] at hC
      rcases hC with hC | rfl
      · exact ih C hC
      · exact ha i
  | resolve cs hp A B hA hB C hC ih =>
      intro D hD
      simp only [List.mem_append, List.mem_singleton] at hD
      rcases hD with hD | rfl
      · exact ih D hD
      · exact resolution_sound (ih A hA) (ih B hB) hC

theorem refutation_unsatisfiable {F : Fin m → Clause n} {cs : List (Clause n)}
    (hr : ResolutionRefutation F cs) : ¬ Satisfiable F := by
  rintro ⟨a, ha⟩
  exact not_satisfies_empty a (resolutionProof_sound hr.1 ha ∅ hr.2)

/--
Minimum resolution length. It is `0` exactly when no refutation exists; this
makes the definition total without assigning an artificial infinite natural.
-/
noncomputable def resolutionComplexity (F : Fin m → Clause n) : Nat :=
  by
    classical
    exact if h : ∃ N, ∃ cs, ResolutionRefutation F cs ∧ cs.length = N then
      Nat.find h
    else 0

theorem resolutionComplexity_eq_zero_of_no_refutation (F : Fin m → Clause n)
    (h : ¬ ∃ cs, ResolutionRefutation F cs) :
    resolutionComplexity F = 0 := by
  classical
  simp only [resolutionComplexity]
  split <;> rename_i hN
  · rcases hN with ⟨N, cs, hcs, _⟩
    exact absurd ⟨cs, hcs⟩ h
  · rfl

theorem resolutionComplexity_spec {F : Fin m → Clause n}
    (h : ∃ cs, ResolutionRefutation F cs) :
    ∃ cs, ResolutionRefutation F cs ∧
      cs.length = resolutionComplexity F := by
  classical
  let hN : ∃ N, ∃ cs, ResolutionRefutation F cs ∧ cs.length = N :=
    ⟨h.choose.length, h.choose, h.choose_spec, rfl⟩
  rw [resolutionComplexity, dif_pos hN]
  exact Nat.find_spec hN

theorem resolutionComplexity_minimal {F : Fin m → Clause n} {cs : List (Clause n)}
    (hcs : ResolutionRefutation F cs) :
    resolutionComplexity F ≤ cs.length := by
  classical
  let hN : ∃ N, ∃ ds, ResolutionRefutation F ds ∧ ds.length = N :=
    ⟨cs.length, cs, hcs, rfl⟩
  rw [resolutionComplexity, dif_pos hN]
  exact Nat.find_min' hN ⟨cs, hcs, rfl⟩

end AvgCaseMls.Section3
