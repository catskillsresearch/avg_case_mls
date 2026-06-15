/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.EMLS

/-!
FOS80 §3 decision procedure for MLS / EMLS **satisfiability** (Phase **2C**).

Steps 2–4 are implemented; Step 1 substitution remains open. **Soundness** and **partial completeness**
on `InDecideSoundFragment` / `InDecideSoundFormula` are proved; global completeness remains open
— see [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md).
-/

namespace MLS

open EMLS

theorem List_any_iff {α} (l : List α) (p : α → Bool) :
    l.any p = true ↔ ∃ x, x ∈ l ∧ p x = true := by
  induction l with
  | nil => simp
  | cons y ys ih =>
    rw [List.any, Bool.or_eq_true, ih]
    constructor
    · intro h
      cases h with
      | inl hp => exact ⟨y, by simp, hp⟩
      | inr h => obtain ⟨x, hx, hpx⟩ := h; exact ⟨x, by simp [hx], hpx⟩
    · intro ⟨x, hx, hpx⟩
      rw [List.mem_cons] at hx
      cases hx with
      | inl hx => subst hx; exact Or.inl hpx
      | inr hx => exact Or.inr ⟨x, hx, hpx⟩

/-! ### Formula → EMLS conjunct (Step 0 / partial Step 1) -/

def formulaToConjunct? : Formula → Option Conjunct
  | Formula.rel r =>
      EMLS.relationToLiteral? r |>.map List.singleton
  | Formula.and f1 f2 => do
      let c1 ← formulaToConjunct? f1
      let c2 ← formulaToConjunct? f2
      return c1 ++ c2
  | _ => none

theorem formulaToConjunct?_and (f1 f2 : Formula) (c1 c2 : Conjunct)
    (h1 : formulaToConjunct? f1 = some c1) (h2 : formulaToConjunct? f2 = some c2) :
    formulaToConjunct? (Formula.and f1 f2) = some (c1 ++ c2) := by
  simp [formulaToConjunct?, h1, h2]

theorem formulaToConjunct?_satisfies (f : Formula) (c : Conjunct)
    (hc : formulaToConjunct? f = some c) (env : Env)
    (h : ∀ lit ∈ c, Literal.holds env lit) : evalFormula env f := by
  match f with
  | Formula.rel r =>
    cases hl : relationToLiteral? r with
    | none => simp [formulaToConjunct?, hl] at hc
    | some lit =>
      simp [formulaToConjunct?, hl] at hc
      subst hc
      exact (relationToLiteral?_eval env r lit hl).mpr (h lit (List.mem_singleton_self lit))
  | Formula.and f1 f2 =>
    cases hc1 : formulaToConjunct? f1 with
    | none => simp [formulaToConjunct?, hc1] at hc
    | some c1 =>
      cases hc2 : formulaToConjunct? f2 with
      | none => simp [formulaToConjunct?, hc2] at hc
      | some c2 =>
        simp [formulaToConjunct?, hc1, hc2] at hc
        subst hc
        exact And.intro
          (formulaToConjunct?_satisfies f1 c1 hc1 env fun lit hl =>
            h lit (List.mem_append.mpr (Or.inl hl)))
          (formulaToConjunct?_satisfies f2 c2 hc2 env fun lit hl =>
            h lit (List.mem_append.mpr (Or.inr hl)))
  | Formula.not _ =>
    simp [formulaToConjunct?] at hc
  | Formula.or _ _ =>
    simp [formulaToConjunct?] at hc
  | Formula.imp _ _ =>
    simp [formulaToConjunct?] at hc
  | Formula.iff _ _ =>
    simp [formulaToConjunct?] at hc

/-! ### FOS80 Step 2 -/

def hasStep2Contradiction (c : Conjunct) : Bool :=
  c.any fun lit1 =>
    c.any fun lit2 =>
      match lit1, lit2 with
      | .neq x y, _ => decide (x = y)
      | .mem x y, .notMem x' y' => decide (x = x' && y = y')
      | _, _ => false

/-! ### FOS80 Step 3 -/

def hasMembershipLiteral (c : Conjunct) : Bool :=
  c.any fun
    | .mem _ _ | .notMem _ _ => true
    | _ => false

def hasStep3Obstruction (c : Conjunct) : Bool :=
  (neqLiterals c).any fun (x, y) =>
    decide (x ≠ y && hasEqEmpty c x && hasEqEmpty c y)

noncomputable def witnessEnv (c : Conjunct) : Env :=
  fun n => if hasEqEmpty c n then ZFSet.empty else ZFSet.tag n

/-! ### Literal / conjunct helpers -/

theorem hasEqEmpty_of_mem (c : Conjunct) (x : Nat) (hx : .eqEmpty x ∈ c) :
    hasEqEmpty c x = true := by
  rw [hasEqEmpty, List_any_iff]
  exact ⟨.eqEmpty x, hx, by simp⟩

theorem hasEqOpLiteral_of_eqOp (c : Conjunct) (x y z : Nat) (op : BinOp)
    (hx : .eqOp x y z op ∈ c) : hasEqOpLiteral c = true := by
  rw [hasEqOpLiteral, List_any_iff]
  exact ⟨.eqOp x y z op, hx, by simp⟩

theorem hasMembershipLiteral_of_mem (c : Conjunct) (x y : Nat) (hx : .mem x y ∈ c) :
    hasMembershipLiteral c = true := by
  rw [hasMembershipLiteral, List_any_iff]
  exact ⟨.mem x y, hx, by simp⟩

theorem hasMembershipLiteral_of_notMem (c : Conjunct) (x y : Nat) (hx : .notMem x y ∈ c) :
    hasMembershipLiteral c = true := by
  rw [hasMembershipLiteral, List_any_iff]
  exact ⟨.notMem x y, hx, by simp⟩

theorem hasStep2_of_neq_refl (c : Conjunct) (x : Nat) (hx : .neq x x ∈ c) :
    hasStep2Contradiction c = true := by
  unfold hasStep2Contradiction
  rw [List_any_iff]
  refine ⟨.neq x x, hx, ?_⟩
  rw [List_any_iff]
  exact ⟨.neq x x, hx, by simp⟩

theorem hasStep2_of_mem_notMem (c : Conjunct) (x y : Nat) (hmem : .mem x y ∈ c)
    (hnot : .notMem x y ∈ c) : hasStep2Contradiction c = true := by
  unfold hasStep2Contradiction
  rw [List_any_iff]
  refine ⟨.mem x y, hmem, ?_⟩
  rw [List_any_iff]
  exact ⟨.notMem x y, hnot, by simp⟩

theorem hasStep3Obstruction_of (c : Conjunct) (x y : Nat) (hxy : x ≠ y)
    (hx : hasEqEmpty c x = true) (hy : hasEqEmpty c y = true) (hne : .neq x y ∈ c) :
    hasStep3Obstruction c = true := by
  unfold hasStep3Obstruction
  rw [List_any_iff]
  refine ⟨(x, y), ?_, ?_⟩
  · simp [neqLiterals, List.mem_filterMap]
    exact ⟨.neq x y, hne, rfl⟩
  · simp [hxy, hx, hy]

namespace Step2

theorem neq_refl_unsat (env : Env) (x : Nat) : ¬ Literal.holds env (.neq x x) := by
  simp [Literal.holds, evalTerm]

theorem mem_notMem_unsat (env : Env) (x y : Nat) :
    ¬ (Literal.holds env (.mem x y) ∧ Literal.holds env (.notMem x y)) := by
  intro ⟨hmem, hnot⟩
  exact hnot hmem

theorem unsat (c : Conjunct) (h : hasStep2Contradiction c = true) :
    ¬ ∃ env, ∀ lit ∈ c, Literal.holds env lit := by
  intro ⟨env, hall⟩
  unfold hasStep2Contradiction at h
  rw [List_any_iff] at h
  obtain ⟨lit1, hl1, h1⟩ := h
  rw [List_any_iff] at h1
  obtain ⟨lit2, hl2, h2⟩ := h1
  cases lit1 with
  | neq x y =>
    have hxy : x = y := by simpa using h2
    subst hxy
    exact neq_refl_unsat env x (hall _ hl1)
  | mem x y =>
    cases lit2 with
    | notMem x' y' =>
      have hpair : x = x' ∧ y = y' := by
        simp [Bool.and_eq_true, decide_eq_true_iff] at h2
        exact h2
      rcases hpair with ⟨rfl, rfl⟩
      exact mem_notMem_unsat env x y ⟨hall _ hl1, hall _ hl2⟩
    | _ => simp at h2
  | _ => simp at h2

end Step2

namespace Step3

theorem witness_eqEmpty (c : Conjunct) (x : Nat) (hx : .eqEmpty x ∈ c) :
    Literal.holds (witnessEnv c) (.eqEmpty x) := by
  have he := hasEqEmpty_of_mem c x hx
  simp [Literal.holds, witnessEnv, he, evalTerm]

theorem witness_neq (c : Conjunct) (x y : Nat) (hxy : x ≠ y) (_hne : .neq x y ∈ c)
    (hob : hasStep3Obstruction c = false) :
    Literal.holds (witnessEnv c) (.neq x y) := by
  simp only [Literal.holds, witnessEnv, evalTerm]
  by_cases hx : hasEqEmpty c x = true
  · by_cases hy : hasEqEmpty c y = true
    · exact absurd (hasStep3Obstruction_of c x y hxy hx hy _hne) (by simpa using hob)
    · simp [hx, hy]
      exact Ne.symm (ZFSet.tag_ne_empty y)
  · by_cases hy : hasEqEmpty c y = true
    · simp [hx, hy]
      exact ZFSet.tag_ne_empty x
    · simp [hx, hy, ZFSet.tag_injective.ne hxy]

theorem witness (c : Conjunct) (h2 : hasStep2Contradiction c = false)
    (hmem : hasMembershipLiteral c = false) (hop : hasEqOpLiteral c = false)
    (h3 : hasStep3Obstruction c = false) :
    ∃ env, ∀ lit ∈ c, Literal.holds env lit := by
  refine ⟨witnessEnv c, fun lit hl => ?_⟩
  cases lit with
  | eqOp x y z op =>
    exact absurd (hasEqOpLiteral_of_eqOp c x y z op hl) (by simpa using hop)
  | eqEmpty x =>
    exact witness_eqEmpty c x hl
  | mem x y =>
    exact absurd (hasMembershipLiteral_of_mem c x y hl) (by simpa using hmem)
  | notMem x y =>
    exact absurd (hasMembershipLiteral_of_notMem c x y hl) (by simpa using hmem)
  | neq x y =>
    by_cases hxy : x = y
    · exact absurd (hasStep2_of_neq_refl c x (by simpa [hxy] using hl)) (by simpa using h2)
    · exact witness_neq c x y hxy hl h3

end Step3

/-! ### FOS80 Step 4 (partial) -/

/-- Syntactic membership-cycle check; self-loops refuted semantically by [`EMLS.step4_self_loop_unsat`]. -/

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
    (notMem.any fun (x, y) => decide (x = y && mem.contains (x, y)))

/-! ### Decision -/

def decideConjunct (c : Conjunct) : Bool :=
  if hasStep2Contradiction c then false
  else if hasStep3Obstruction c then false
  else if !hasMembershipLiteral c then true
  else if hasStep4Obstruction c then false
  else true

theorem decideConjunct_true_of_step3 (c : Conjunct)
    (h2 : hasStep2Contradiction c = false) (h3o : hasStep3Obstruction c = false)
    (hmem : hasMembershipLiteral c = false) :
    decideConjunct c = true := by
  simp [decideConjunct, h2, h3o, hmem]

def decideEMLSSat (c : Conjunct) : Bool :=
  decideConjunct c

def decideMLSSat (f : Formula) : Bool :=
  match formulaToConjunct? f with
  | some c => decideConjunct c
  | none =>
      match f with
      | Formula.rel (Relation.eq Term.empty Term.empty) => true
      | Formula.rel (Relation.neq Term.empty Term.empty) => false
      | _ => false

def decideEMLSSat? (c : Conjunct) : Option Bool :=
  conjunctToFormula c |>.map decideMLSSat

abbrev decideMLS := decideMLSSat

/-! ### Sound fragment -/

def InDecideSoundFragment (c : Conjunct) : Prop :=
  hasStep2Contradiction c = false ∧
  hasStep3Obstruction c = false ∧
  hasMembershipLiteral c = false ∧
  hasEqOpLiteral c = false

theorem decideConjunct_sound (c : Conjunct) (_h : decideConjunct c = true)
    (hfrag : InDecideSoundFragment c) :
    ∃ env, ∀ lit ∈ c, Literal.holds env lit :=
  Step3.witness c hfrag.1 hfrag.2.2.1 hfrag.2.2.2 hfrag.2.1

theorem decideConjunct_unsat_step2 (c : Conjunct) (h2 : hasStep2Contradiction c = true) :
    decideConjunct c = false := by simp [decideConjunct, h2]

theorem decideConjunct_refutes_step2 (c : Conjunct) (h2 : hasStep2Contradiction c = true) :
    ¬ ∃ env, ∀ lit ∈ c, Literal.holds env lit :=
  Step2.unsat c h2

def InDecideSoundFormula (f : Formula) : Prop :=
  ∃ c, formulaToConjunct? f = some c ∧ InDecideSoundFragment c

theorem decideMLSSat_sound (f : Formula) (h : decideMLSSat f = true)
    (hfrag : InDecideSoundFormula f) :
    ∃ env, evalFormula env f := by
  obtain ⟨c, hc, hfragc⟩ := hfrag
  simp [decideMLSSat, hc] at h
  obtain ⟨env, henv⟩ := decideConjunct_sound c h hfragc
  exact ⟨env, formulaToConjunct?_satisfies f c hc env henv⟩

theorem decideMLS_sound (f : Formula) (h : decideMLS f = true)
    (hfrag : InDecideSoundFormula f) :
    ∃ env, evalFormula env f :=
  decideMLSSat_sound f h hfrag

/-! ### Partial completeness (sound, membership-free fragment) -/

/--
On the sound fragment, [`decideConjunct`] never returns `false`: Step 2/3 do not fire and
membership literals are absent, so the procedure accepts after the membership guard.
-/
theorem decideConjunct_complete_sound_fragment (c : Conjunct) (hfrag : InDecideSoundFragment c) :
    decideConjunct c = true := by
  unfold decideConjunct
  have h2 := hfrag.1
  have h3 := hfrag.2.1
  have hmem := hfrag.2.2.1
  simp [h2, h3, hmem]

/--
Formula-level partial completeness: on [`InDecideSoundFormula`], [`decideMLSSat`] returns `true`.
-/
theorem decideMLSSat_complete_sound_fragment (f : Formula) (hfrag : InDecideSoundFormula f) :
    decideMLSSat f = true := by
  obtain ⟨c, hc, hfragc⟩ := hfrag
  simp [decideMLSSat, hc]
  exact decideConjunct_complete_sound_fragment c hfragc

theorem decideMLS_complete_sound_fragment (f : Formula) (hfrag : InDecideSoundFormula f) :
    decideMLS f = true :=
  decideMLSSat_complete_sound_fragment f hfrag

/-! ### Global completeness — not proved (Step 1 / full Step 4 open) -/

/--
Full FOS80 completeness: requires Step 1 substitution and complete Step 4 model search.
See [`decideMLSSat_complete_sound_fragment`] for the verified membership-free sound fragment.
-/
theorem decideMLSSat_complete (f : Formula) (_h : ∃ env, evalFormula env f) :
    decideMLSSat f = true := by
  sorry

theorem decideMLS_complete (f : Formula) (h : ∃ env, evalFormula env f) :
    decideMLS f = true :=
  decideMLSSat_complete f h

end MLS
