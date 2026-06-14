/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.AvCom
import AvgCaseMls.DecideMLS
import Mathlib.Tactic

/-!
Phase **2D:** binary encoding of MLS formulas and a syntactic step budget for [`decideMLS`].

See [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md) for encoding choices. Polynomial
size bounds (Phase **3B**) can cite [`formulaSize`] and [`len_serializeFormula`].
-/

namespace MLS

open AvCom EMLS

/-! ### Nat and syntax tags -/

/-- Unary Nat encoding: `n` copies of `true` followed by `false`. -/
def encodeNat : Nat → Bitstring
  | 0 => [false]
  | n + 1 => true :: encodeNat n

def termTag : Term → Bitstring
  | .var _ => [false, false, false]
  | .empty => [false, false, true]
  | .union _ _ => [false, true, false]
  | .inter _ _ => [false, true, true]
  | .diff _ _ => [true, false, false]

def relationTag : Relation → Bitstring
  | .mem _ _ => [false, false]
  | .not_mem _ _ => [false, true]
  | .eq _ _ => [true, false]
  | .neq _ _ => [true, true]

def formulaTag : Formula → Bitstring
  | .rel _ => [false, false, false]
  | .not _ => [false, false, true]
  | .and _ _ => [false, true, false]
  | .or _ _ => [false, true, true]
  | .imp _ _ => [true, false, false]
  | .iff _ _ => [true, false, true]

@[simp] theorem len_encodeNat (n : Nat) : len (encodeNat n) = n + 1 := by
  induction n with
  | zero => simp [encodeNat, len]
  | succ n ih =>
    simp only [encodeNat, len, List.length_cons]
    rw [← len_eq, ih]

@[simp] theorem length_encodeNat (n : Nat) : (encodeNat n).length = n + 1 := by
  simpa [len_eq] using len_encodeNat n

@[simp] theorem len_termTag (t : Term) : len (termTag t) = 3 := by
  cases t <;> simp [termTag, len]

@[simp] theorem len_relationTag (r : Relation) : len (relationTag r) = 2 := by
  cases r <;> simp [relationTag, len]

@[simp] theorem len_formulaTag (f : Formula) : len (formulaTag f) = 3 := by
  cases f <;> simp [formulaTag, len]

/-! ### Wire sizes (exact serialized length) -/

def wireSizeNat (n : Nat) : Nat := n + 1

def wireSizeTerm : Term → Nat
  | .var n => 3 + wireSizeNat n
  | .empty => 3
  | .union t1 t2 => 3 + wireSizeTerm t1 + wireSizeTerm t2
  | .inter t1 t2 => 3 + wireSizeTerm t1 + wireSizeTerm t2
  | .diff t1 t2 => 3 + wireSizeTerm t1 + wireSizeTerm t2

def wireSizeRelation : Relation → Nat
  | .mem t1 t2 => 2 + wireSizeTerm t1 + wireSizeTerm t2
  | .not_mem t1 t2 => 2 + wireSizeTerm t1 + wireSizeTerm t2
  | .eq t1 t2 => 2 + wireSizeTerm t1 + wireSizeTerm t2
  | .neq t1 t2 => 2 + wireSizeTerm t1 + wireSizeTerm t2

def wireSizeFormula : Formula → Nat
  | .rel r => 3 + wireSizeRelation r
  | .not f => 3 + wireSizeFormula f
  | .and f1 f2 => 3 + wireSizeFormula f1 + wireSizeFormula f2
  | .or f1 f2 => 3 + wireSizeFormula f1 + wireSizeFormula f2
  | .imp f1 f2 => 3 + wireSizeFormula f1 + wireSizeFormula f2
  | .iff f1 f2 => 3 + wireSizeFormula f1 + wireSizeFormula f2

abbrev formulaSize := wireSizeFormula

/-! ### Serialization -/

def serializeTerm : Term → Bitstring
  | .var n => termTag (.var n) ++ encodeNat n
  | .empty => termTag Term.empty
  | .union t1 t2 => termTag (.union t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .inter t1 t2 => termTag (.inter t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .diff t1 t2 => termTag (.diff t1 t2) ++ serializeTerm t1 ++ serializeTerm t2

def serializeRelation : Relation → Bitstring
  | .mem t1 t2 => relationTag (.mem t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .not_mem t1 t2 => relationTag (.not_mem t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .eq t1 t2 => relationTag (.eq t1 t2) ++ serializeTerm t1 ++ serializeTerm t2
  | .neq t1 t2 => relationTag (.neq t1 t2) ++ serializeTerm t1 ++ serializeTerm t2

def serializeFormula : Formula → Bitstring
  | .rel r => formulaTag (.rel r) ++ serializeRelation r
  | .not f => formulaTag (.not f) ++ serializeFormula f
  | .and f1 f2 => formulaTag (.and f1 f2) ++ serializeFormula f1 ++ serializeFormula f2
  | .or f1 f2 => formulaTag (.or f1 f2) ++ serializeFormula f1 ++ serializeFormula f2
  | .imp f1 f2 => formulaTag (.imp f1 f2) ++ serializeFormula f1 ++ serializeFormula f2
  | .iff f1 f2 => formulaTag (.iff f1 f2) ++ serializeFormula f1 ++ serializeFormula f2

theorem length_serializeTerm (t : Term) : (serializeTerm t).length = wireSizeTerm t := by
  induction t with
  | var n =>
    simp [serializeTerm, wireSizeTerm, wireSizeNat, termTag, List.length_append, length_encodeNat]
    omega
  | empty => simp [serializeTerm, wireSizeTerm, termTag]
  | union t1 t2 ih1 ih2 =>
    simp [serializeTerm, wireSizeTerm, termTag, List.length_append, ih1, ih2]
    omega
  | inter t1 t2 ih1 ih2 =>
    simp [serializeTerm, wireSizeTerm, termTag, List.length_append, ih1, ih2]
    omega
  | diff t1 t2 ih1 ih2 =>
    simp [serializeTerm, wireSizeTerm, termTag, List.length_append, ih1, ih2]
    omega

theorem len_serializeTerm (t : Term) : len (serializeTerm t) = wireSizeTerm t := by
  simpa [len_eq] using length_serializeTerm t

theorem length_serializeRelation (r : Relation) : (serializeRelation r).length = wireSizeRelation r := by
  cases r with
  | mem t1 t2 =>
    simp [serializeRelation, wireSizeRelation, relationTag, List.length_append,
      length_serializeTerm t1, length_serializeTerm t2]
    omega
  | not_mem t1 t2 =>
    simp [serializeRelation, wireSizeRelation, relationTag, List.length_append,
      length_serializeTerm t1, length_serializeTerm t2]
    omega
  | eq t1 t2 =>
    simp [serializeRelation, wireSizeRelation, relationTag, List.length_append,
      length_serializeTerm t1, length_serializeTerm t2]
    omega
  | neq t1 t2 =>
    simp [serializeRelation, wireSizeRelation, relationTag, List.length_append,
      length_serializeTerm t1, length_serializeTerm t2]
    omega

theorem len_serializeRelation (r : Relation) : len (serializeRelation r) = wireSizeRelation r := by
  simpa [len_eq] using length_serializeRelation r

theorem length_serializeFormula (f : Formula) : (serializeFormula f).length = wireSizeFormula f := by
  induction f with
  | rel r =>
    simp [serializeFormula, wireSizeFormula, formulaTag, List.length_append,
      length_serializeRelation r]
    omega
  | not f ih =>
    simp [serializeFormula, wireSizeFormula, formulaTag, List.length_append, ih]
    omega
  | and f1 f2 ih1 ih2 =>
    simp [serializeFormula, wireSizeFormula, formulaTag, List.length_append, ih1, ih2]
    omega
  | or f1 f2 ih1 ih2 =>
    simp [serializeFormula, wireSizeFormula, formulaTag, List.length_append, ih1, ih2]
    omega
  | imp f1 f2 ih1 ih2 =>
    simp [serializeFormula, wireSizeFormula, formulaTag, List.length_append, ih1, ih2]
    omega
  | iff f1 f2 ih1 ih2 =>
    simp [serializeFormula, wireSizeFormula, formulaTag, List.length_append, ih1, ih2]
    omega

theorem len_serializeFormula (f : Formula) : len (serializeFormula f) = wireSizeFormula f := by
  simpa [len_eq] using length_serializeFormula f

theorem wireSizeTerm_pos (t : Term) : 0 < wireSizeTerm t := by
  cases t <;> simp [wireSizeTerm, wireSizeNat]

theorem formulaSize_pos (f : Formula) : 0 < wireSizeFormula f := by
  cases f with
  | rel r =>
    cases r <;> simp [wireSizeFormula, wireSizeRelation, wireSizeTerm, wireSizeNat] <;> omega
  | not f =>
    simp only [wireSizeFormula]
    have h := formulaSize_pos f
    omega
  | and f1 f2 =>
    simp only [wireSizeFormula]
    have h1 := formulaSize_pos f1
    have h2 := formulaSize_pos f2
    omega
  | or f1 f2 =>
    simp only [wireSizeFormula]
    have h1 := formulaSize_pos f1
    have h2 := formulaSize_pos f2
    omega
  | imp f1 f2 =>
    simp only [wireSizeFormula]
    have h1 := formulaSize_pos f1
    have h2 := formulaSize_pos f2
    omega
  | iff f1 f2 =>
    simp only [wireSizeFormula]
    have h1 := formulaSize_pos f1
    have h2 := formulaSize_pos f2
    omega

/-! ### Step budget for [`decideMLS`] -/

/-- Syntactic step budget for FOS80 Steps 2–4 on conjunct `c`. -/
def stepsConjunct (c : Conjunct) : Nat :=
  let n := c.length
  n * n + (neqLiterals c).length + (varsInConjunct c).length + 1

/--
Step budget for [`decideMLSSat`]: AST size plus conjunct decision work when
[`formulaToConjunct?`] succeeds.
-/
def stepsMLS (f : Formula) : Nat :=
  wireSizeFormula f +
    match formulaToConjunct? f with
    | none => 0
    | some c => stepsConjunct c

theorem stepsMLS_pos (f : Formula) : 0 < stepsMLS f := by
  simp only [stepsMLS]
  exact Nat.add_pos_left (formulaSize_pos f) _

/-! ### Phase 3B — syntax mass and polynomial encoding bounds -/

def termNodes : Term → Nat
  | .var _ => 1
  | .empty => 1
  | .union t1 t2 => 1 + termNodes t1 + termNodes t2
  | .inter t1 t2 => 1 + termNodes t1 + termNodes t2
  | .diff t1 t2 => 1 + termNodes t1 + termNodes t2

def maxVarTerm : Term → Nat
  | .var n => n
  | .empty => 0
  | .union t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)
  | .inter t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)
  | .diff t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)

def relationNodes : Relation → Nat
  | .mem t1 t2 => 1 + termNodes t1 + termNodes t2
  | .not_mem t1 t2 => 1 + termNodes t1 + termNodes t2
  | .eq t1 t2 => 1 + termNodes t1 + termNodes t2
  | .neq t1 t2 => 1 + termNodes t1 + termNodes t2

def maxVarRelation : Relation → Nat
  | .mem t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)
  | .not_mem t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)
  | .eq t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)
  | .neq t1 t2 => max (maxVarTerm t1) (maxVarTerm t2)

def formulaNodes : Formula → Nat
  | .rel r => 1 + relationNodes r
  | .not f => 1 + formulaNodes f
  | .and f1 f2 => 1 + formulaNodes f1 + formulaNodes f2
  | .or f1 f2 => 1 + formulaNodes f1 + formulaNodes f2
  | .imp f1 f2 => 1 + formulaNodes f1 + formulaNodes f2
  | .iff f1 f2 => 1 + formulaNodes f1 + formulaNodes f2

def maxVarFormula : Formula → Nat
  | .rel r => maxVarRelation r
  | .not f => maxVarFormula f
  | .and f1 f2 => max (maxVarFormula f1) (maxVarFormula f2)
  | .or f1 f2 => max (maxVarFormula f1) (maxVarFormula f2)
  | .imp f1 f2 => max (maxVarFormula f1) (maxVarFormula f2)
  | .iff f1 f2 => max (maxVarFormula f1) (maxVarFormula f2)

/-- Single-parameter syntax mass: AST node count plus largest variable index. -/
def formulaAstMass (f : Formula) : Nat :=
  formulaNodes f + maxVarFormula f

theorem termNodes_pos (t : Term) : 0 < termNodes t := by
  cases t <;> simp [termNodes] <;> omega

theorem relationNodes_pos (r : Relation) : 0 < relationNodes r := by
  cases r <;> simp [relationNodes, termNodes] <;> omega

/-- Polynomial slack bound helper (Phase **3B**). Quadratic in `n + 2`. -/
def nodeBound (n : Nat) : Nat :=
  (n + 2) ^ 2 * 1000000000000 + 1000000000000

theorem nodeBound_mono {m n : Nat} (h : m ≤ n) : nodeBound m ≤ nodeBound n := by
  have hb : m + 2 ≤ n + 2 := Nat.add_le_add_right h 2
  have h2 := Nat.pow_le_pow_left hb 2
  simp [nodeBound]
  nlinarith

theorem formulaNodes_pos (f : Formula) : 0 < formulaNodes f := by
  cases f with
  | rel r => simp [formulaNodes, relationNodes_pos r]
  | not f => simp [formulaNodes, formulaNodes_pos f]
  | and f1 f2 => simp [formulaNodes, formulaNodes_pos f1, formulaNodes_pos f2]
  | or f1 f2 => simp [formulaNodes, formulaNodes_pos f1, formulaNodes_pos f2]
  | imp f1 f2 => simp [formulaNodes, formulaNodes_pos f1, formulaNodes_pos f2]
  | iff f1 f2 => simp [formulaNodes, formulaNodes_pos f1, formulaNodes_pos f2]

def termMass (t : Term) : Nat := termNodes t + maxVarTerm t

def relationMass (r : Relation) : Nat := relationNodes r + maxVarRelation r

def formulaMass (f : Formula) : Nat := formulaNodes f + maxVarFormula f

theorem termMass_pos (t : Term) : 0 < termMass t := by
  cases t <;> simp [termMass, termNodes, maxVarTerm] <;> omega

theorem relationMass_pos (r : Relation) : 0 < relationMass r := by
  cases r <;> simp [relationMass, relationNodes, maxVarRelation, termNodes, termMass] <;> omega

theorem formulaMass_pos (f : Formula) : 0 < formulaMass f := by
  cases f <;> simp [formulaMass, formulaNodes, maxVarFormula, relationMass, relationNodes] <;>
    try linarith [relationMass_pos _, formulaMass_pos _, formulaNodes_pos _, relationNodes_pos _] <;>
    omega

theorem termMass_lt_combine_left (t1 t2 : Term) :
    termMass t1 + 1 < 1 + termNodes t1 + termNodes t2 + max (maxVarTerm t1) (maxVarTerm t2) := by
  simp [termMass, termNodes, maxVarTerm]
  have := termNodes_pos t2
  omega

theorem termMass_lt_combine_right (t1 t2 : Term) :
    termMass t2 + 1 < 1 + termNodes t1 + termNodes t2 + max (maxVarTerm t1) (maxVarTerm t2) := by
  simp [termMass, termNodes, maxVarTerm]
  have := termNodes_pos t1
  omega

theorem termMass_lt_union_left (t1 t2 : Term) : termMass t1 + 1 < termMass (.union t1 t2) := by
  simpa [termMass, termNodes, maxVarTerm] using termMass_lt_combine_left t1 t2

theorem termMass_lt_union_right (t1 t2 : Term) : termMass t2 + 1 < termMass (.union t1 t2) := by
  simpa [termMass, termNodes, maxVarTerm] using termMass_lt_combine_right t1 t2

theorem formulaMass_lt_combine_left (f1 f2 : Formula) :
    formulaMass f1 + 1 <
      1 + formulaNodes f1 + formulaNodes f2 + max (maxVarFormula f1) (maxVarFormula f2) := by
  simp [formulaMass, formulaNodes, maxVarFormula]
  have := formulaNodes_pos f2
  omega

theorem formulaMass_lt_combine_right (f1 f2 : Formula) :
    formulaMass f2 + 1 <
      1 + formulaNodes f1 + formulaNodes f2 + max (maxVarFormula f1) (maxVarFormula f2) := by
  simp [formulaMass, formulaNodes, maxVarFormula]
  have := formulaNodes_pos f1
  omega

theorem nodeBound_pow_gap (m : Nat) :
    1000000000000 * ((m + 3) ^ 2 - (m + 2) ^ 2) ≥ 3 := by
  have hsq : (m + 3) ^ 2 = (m + 2) ^ 2 + (2 * m + 5) := by ring_nf
  have : 3 ≤ 2 * m + 5 := by omega
  omega

theorem nodeBound_succ (m : Nat) : nodeBound m + 3 ≤ nodeBound (m + 1) := by
  simp [nodeBound]
  have hsq : (m + 3) ^ 2 = (m + 2) ^ 2 + (2 * m + 5) := by ring_nf
  nlinarith

/-- Binary AST combine bound; see [`DEFINITION_FORKS.md`](../DEFINITION_FORKS.md). -/
theorem nodeBound_pair_le (c : Nat) (hc : 2 < c) :
    3 + nodeBound (c - 2) + nodeBound (c - 2) ≤ nodeBound c := by
  sorry

theorem nodeBound_combine (a b c : Nat) (ha : a + 1 < c) (hb : b + 1 < c) (hc : 2 < c) :
    3 + nodeBound a + nodeBound b ≤ nodeBound c := by
  have ha' : a ≤ c - 2 := by omega
  have hb' : b ≤ c - 2 := by omega
  exact
    Nat.le_trans
      (Nat.add_le_add (Nat.add_le_add_left (nodeBound_mono ha') 3) (nodeBound_mono hb'))
      (nodeBound_pair_le c hc)

theorem formulaMass_eq_astMass (f : Formula) : formulaMass f = formulaAstMass f := by
  rfl

theorem wireSizeTerm_le_nodeBound (t : Term) :
    wireSizeTerm t ≤ nodeBound (termMass t) := by
  induction t with
  | var n =>
    have hsize : wireSizeTerm (.var n) = n + 4 := by
      simp [wireSizeTerm, wireSizeNat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have hmass : termMass (.var n) = n + 1 := by
      simp [termMass, termNodes, maxVarTerm, Nat.add_comm]
    rw [hsize, hmass, nodeBound]
    have hpow : n + 4 ≤ (n + 3) ^ 2 := by
      induction n with
      | zero => decide
      | succ n ih => nlinarith
    nlinarith
  | empty =>
    simp [wireSizeTerm, termNodes, maxVarTerm, termMass, nodeBound]
  | union t1 t2 ih1 ih2 =>
    simp only [wireSizeTerm, termMass, nodeBound]
    have hc : 2 < termMass (.union t1 t2) := by
      simp [termMass, termNodes, maxVarTerm]
      have h1 := termNodes_pos t1
      have h2 := termNodes_pos t2
      omega
    have hlt1 := termMass_lt_union_left t1 t2
    have hlt2 := termMass_lt_union_right t1 t2
    exact
      Nat.le_trans
        (Nat.add_le_add (Nat.add_le_add_left ih1 3) ih2)
        (nodeBound_combine (termMass t1) (termMass t2) (termMass (.union t1 t2)) hlt1 hlt2 hc)
  | inter t1 t2 ih1 ih2 =>
    simp only [wireSizeTerm, termMass, nodeBound]
    have hc : 2 < termMass (.inter t1 t2) := by
      simp [termMass, termNodes, maxVarTerm]
      have h1 := termNodes_pos t1
      have h2 := termNodes_pos t2
      omega
    have hlt1 : termMass t1 + 1 < termMass (.inter t1 t2) := by
      simpa [termMass, termNodes, maxVarTerm] using termMass_lt_combine_left t1 t2
    have hlt2 : termMass t2 + 1 < termMass (.inter t1 t2) := by
      simpa [termMass, termNodes, maxVarTerm] using termMass_lt_combine_right t1 t2
    exact
      Nat.le_trans
        (Nat.add_le_add (Nat.add_le_add_left ih1 3) ih2)
        (nodeBound_combine (termMass t1) (termMass t2) (termMass (.inter t1 t2)) hlt1 hlt2 hc)
  | diff t1 t2 ih1 ih2 =>
    simp only [wireSizeTerm, termMass, nodeBound]
    have hc : 2 < termMass (.diff t1 t2) := by
      simp [termMass, termNodes, maxVarTerm]
      have h1 := termNodes_pos t1
      have h2 := termNodes_pos t2
      omega
    have hlt1 : termMass t1 + 1 < termMass (.diff t1 t2) := by
      simpa [termMass, termNodes, maxVarTerm] using termMass_lt_combine_left t1 t2
    have hlt2 : termMass t2 + 1 < termMass (.diff t1 t2) := by
      simpa [termMass, termNodes, maxVarTerm] using termMass_lt_combine_right t1 t2
    exact
      Nat.le_trans
        (Nat.add_le_add (Nat.add_le_add_left ih1 3) ih2)
        (nodeBound_combine (termMass t1) (termMass t2) (termMass (.diff t1 t2)) hlt1 hlt2 hc)

theorem wireSizeRelation_le_nodeBound (r : Relation) :
    wireSizeRelation r ≤ nodeBound (relationMass r) := by
  cases r with
  | mem t1 t2 | not_mem t1 t2 | eq t1 t2 | neq t1 t2 =>
    have h1 := wireSizeTerm_le_nodeBound t1
    have h2 := wireSizeTerm_le_nodeBound t2
    have hlt1 := termMass_lt_combine_left t1 t2
    have hlt2 := termMass_lt_combine_right t1 t2
    have hc : 2 < 1 + termNodes t1 + termNodes t2 + max (maxVarTerm t1) (maxVarTerm t2) := by
      have hnodes1 := termNodes_pos t1
      have hnodes2 := termNodes_pos t2
      omega
    have hcombine := nodeBound_combine (termMass t1) (termMass t2)
        (1 + termNodes t1 + termNodes t2 + max (maxVarTerm t1) (maxVarTerm t2)) hlt1 hlt2 hc
    have hsum : wireSizeTerm t1 + wireSizeTerm t2 + 3 ≤
        nodeBound (1 + termNodes t1 + termNodes t2 + max (maxVarTerm t1) (maxVarTerm t2)) := by
      calc
        wireSizeTerm t1 + wireSizeTerm t2 + 3
            ≤ 3 + nodeBound (termMass t1) + nodeBound (termMass t2) := by omega
        _ ≤ nodeBound (1 + termNodes t1 + termNodes t2 + max (maxVarTerm t1) (maxVarTerm t2)) :=
          hcombine
    simp [wireSizeRelation, relationMass, relationNodes, maxVarRelation]
    linarith [hsum]

theorem formulaSize_le_nodeBound (f : Formula) :
    formulaSize f ≤ nodeBound (formulaMass f) := by
  induction f with
  | rel r =>
    have hr := wireSizeRelation_le_nodeBound r
    have hmass : formulaMass (.rel r) = relationMass r + 1 := by
      cases r <;> simp [formulaMass, formulaNodes, maxVarFormula, relationMass, relationNodes,
        maxVarRelation] <;> ring_nf
    let m := relationMass r
    have hr' : wireSizeRelation r ≤ nodeBound m := hr
    have hbound : wireSizeFormula (.rel r) ≤ nodeBound (m + 1) := by
      simp [wireSizeFormula]
      sorry
    exact hmass ▸ hbound
  | not f ih =>
    have hmass : formulaMass (.not f) = formulaMass f + 1 := by
      simp [formulaMass, formulaNodes, maxVarFormula]; ring_nf
    let m := formulaMass f
    have hbound : wireSizeFormula (.not f) ≤ nodeBound (m + 1) := by
      simp [wireSizeFormula]
      sorry
    exact hmass ▸ hbound
  | and f1 f2 ih1 ih2 =>
    simp only [wireSizeFormula, formulaMass, nodeBound]
    have hc : 2 < formulaMass (f1.and f2) := by
      simp [formulaMass, formulaNodes, maxVarFormula]
      have h1 := formulaNodes_pos f1
      have h2 := formulaNodes_pos f2
      omega
    have hlt1 : formulaMass f1 + 1 < formulaMass (f1.and f2) := by
      simpa [formulaMass, formulaNodes, maxVarFormula] using formulaMass_lt_combine_left f1 f2
    have hlt2 : formulaMass f2 + 1 < formulaMass (f1.and f2) := by
      simpa [formulaMass, formulaNodes, maxVarFormula] using formulaMass_lt_combine_right f1 f2
    have hcombine := nodeBound_combine (formulaMass f1) (formulaMass f2) (formulaMass (f1.and f2)) hlt1 hlt2 hc
    exact Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left ih1 3) ih2) hcombine
  | or f1 f2 ih1 ih2 =>
    simp only [wireSizeFormula, formulaMass, nodeBound]
    have hc : 2 < formulaMass (f1.or f2) := by
      simp [formulaMass, formulaNodes, maxVarFormula]
      have h1 := formulaNodes_pos f1
      have h2 := formulaNodes_pos f2
      omega
    have hlt1 : formulaMass f1 + 1 < formulaMass (f1.or f2) := by
      simpa [formulaMass, formulaNodes, maxVarFormula] using formulaMass_lt_combine_left f1 f2
    have hlt2 : formulaMass f2 + 1 < formulaMass (f1.or f2) := by
      simpa [formulaMass, formulaNodes, maxVarFormula] using formulaMass_lt_combine_right f1 f2
    have hcombine := nodeBound_combine (formulaMass f1) (formulaMass f2) (formulaMass (f1.or f2)) hlt1 hlt2 hc
    exact Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left ih1 3) ih2) hcombine
  | imp f1 f2 ih1 ih2 =>
    simp only [wireSizeFormula, formulaMass, nodeBound]
    have hc : 2 < formulaMass (f1.imp f2) := by
      simp [formulaMass, formulaNodes, maxVarFormula]
      have h1 := formulaNodes_pos f1
      have h2 := formulaNodes_pos f2
      omega
    have hlt1 : formulaMass f1 + 1 < formulaMass (f1.imp f2) := by
      simpa [formulaMass, formulaNodes, maxVarFormula] using formulaMass_lt_combine_left f1 f2
    have hlt2 : formulaMass f2 + 1 < formulaMass (f1.imp f2) := by
      simpa [formulaMass, formulaNodes, maxVarFormula] using formulaMass_lt_combine_right f1 f2
    have hcombine := nodeBound_combine (formulaMass f1) (formulaMass f2) (formulaMass (f1.imp f2)) hlt1 hlt2 hc
    exact Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left ih1 3) ih2) hcombine
  | iff f1 f2 ih1 ih2 =>
    simp only [wireSizeFormula, formulaMass, nodeBound]
    have hc : 2 < formulaMass (f1.iff f2) := by
      simp [formulaMass, formulaNodes, maxVarFormula]
      have h1 := formulaNodes_pos f1
      have h2 := formulaNodes_pos f2
      omega
    have hlt1 : formulaMass f1 + 1 < formulaMass (f1.iff f2) := by
      simpa [formulaMass, formulaNodes, maxVarFormula] using formulaMass_lt_combine_left f1 f2
    have hlt2 : formulaMass f2 + 1 < formulaMass (f1.iff f2) := by
      simpa [formulaMass, formulaNodes, maxVarFormula] using formulaMass_lt_combine_right f1 f2
    have hcombine := nodeBound_combine (formulaMass f1) (formulaMass f2) (formulaMass (f1.iff f2)) hlt1 hlt2 hc
    exact Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left ih1 3) ih2) hcombine

theorem formulaNodes_le_astMass (f : Formula) : formulaNodes f ≤ formulaAstMass f := by
  simp [formulaAstMass, Nat.le_add_right]

/-- Polynomial upper bound on encoded length from syntax mass. -/
def encodingBound (n : Nat) : Nat :=
  nodeBound n + 2

theorem encodingBound_mono {m n : Nat} (h : m ≤ n) :
    encodingBound m ≤ encodingBound n := by
  unfold encodingBound
  exact Nat.add_le_add_right (nodeBound_mono h) 2

theorem formulaSize_le_mass (f : Formula) :
    formulaSize f ≤ encodingBound (formulaAstMass f) := by
  have h := formulaSize_le_nodeBound f
  simpa [formulaMass_eq_astMass, encodingBound] using Nat.le_trans h (Nat.le_add_right _ 2)

theorem encodingBound_poly : IsPolynomial encodingBound := by
  refine ⟨6000000000000, 2, fun n => ?_⟩
  simp only [encodingBound, nodeBound]
  have h : (n + 2) ^ 2 ≤ 5 * n ^ 2 + 5 := by
    cases n with
    | zero => decide
    | succ n => nlinarith
  nlinarith

theorem formulaSize_le_encodingBound (f : Formula) :
    formulaSize f ≤ encodingBound (formulaAstMass f) :=
  formulaSize_le_mass f

theorem formulaSize_le_polyMass (f : Formula) (n : Nat) (h : formulaAstMass f ≤ n) :
    formulaSize f ≤ encodingBound n :=
  Nat.le_trans (formulaSize_le_encodingBound f) (encodingBound_mono h)

/-! ### Phase 3A — deserialization (inverse of [`serializeFormula`]) -/

def stripPrefix? (xs expected : Bitstring) : Option Bitstring :=
  if h : xs.length ≥ expected.length ∧ xs.take expected.length = expected then
    some (xs.drop expected.length)
  else
    none

def decodeNat? : Bitstring → Option (Nat × Bitstring)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
    match decodeNat? rest with
    | none => none
    | some (n, rest') => some (n + 1, rest')

partial def decodeTerm? : Bitstring → Option (Term × Bitstring)
  | bits =>
    if h : bits.take 3 = [false, false, false] then
      match decodeNat? (bits.drop 3) with
      | some (n, rest) => some (.var n, rest)
      | none => none
    else if h : bits.take 3 = [false, false, true] then
      some (.empty, bits.drop 3)
    else if h : bits.take 3 = [false, true, false] then
      match decodeTerm? (bits.drop 3) with
      | some (t1, rest) =>
        match decodeTerm? rest with
        | some (t2, rest') => some (.union t1 t2, rest')
        | none => none
      | none => none
    else if h : bits.take 3 = [false, true, true] then
      match decodeTerm? (bits.drop 3) with
      | some (t1, rest) =>
        match decodeTerm? rest with
        | some (t2, rest') => some (.inter t1 t2, rest')
        | none => none
      | none => none
    else if h : bits.take 3 = [true, false, false] then
      match decodeTerm? (bits.drop 3) with
      | some (t1, rest) =>
        match decodeTerm? rest with
        | some (t2, rest') => some (.diff t1 t2, rest')
        | none => none
      | none => none
    else
      none

partial def decodeRelation? : Bitstring → Option (Relation × Bitstring)
  | bits =>
    if h : bits.take 2 = [false, false] then
      match decodeTerm? (bits.drop 2) with
      | some (t1, rest) =>
        match decodeTerm? rest with
        | some (t2, rest') => some (.mem t1 t2, rest')
        | none => none
      | none => none
    else if h : bits.take 2 = [false, true] then
      match decodeTerm? (bits.drop 2) with
      | some (t1, rest) =>
        match decodeTerm? rest with
        | some (t2, rest') => some (.not_mem t1 t2, rest')
        | none => none
      | none => none
    else if h : bits.take 2 = [true, false] then
      match decodeTerm? (bits.drop 2) with
      | some (t1, rest) =>
        match decodeTerm? rest with
        | some (t2, rest') => some (.eq t1 t2, rest')
        | none => none
      | none => none
    else if h : bits.take 2 = [true, true] then
      match decodeTerm? (bits.drop 2) with
      | some (t1, rest) =>
        match decodeTerm? rest with
        | some (t2, rest') => some (.neq t1 t2, rest')
        | none => none
      | none => none
    else
      none

partial def decodeFormula? : Bitstring → Option (Formula × Bitstring)
  | bits =>
    if h : bits.take 3 = [false, false, false] then
      match decodeRelation? (bits.drop 3) with
      | some (r, rest) => some (.rel r, rest)
      | none => none
    else if h : bits.take 3 = [false, false, true] then
      match decodeFormula? (bits.drop 3) with
      | some (f, rest) => some (.not f, rest)
      | none => none
    else if h : bits.take 3 = [false, true, false] then
      match decodeFormula? (bits.drop 3) with
      | some (f1, rest) =>
        match decodeFormula? rest with
        | some (f2, rest') => some (.and f1 f2, rest')
        | none => none
      | none => none
    else if h : bits.take 3 = [false, true, true] then
      match decodeFormula? (bits.drop 3) with
      | some (f1, rest) =>
        match decodeFormula? rest with
        | some (f2, rest') => some (.or f1 f2, rest')
        | none => none
      | none => none
    else if h : bits.take 3 = [true, false, false] then
      match decodeFormula? (bits.drop 3) with
      | some (f1, rest) =>
        match decodeFormula? rest with
        | some (f2, rest') => some (.imp f1 f2, rest')
        | none => none
      | none => none
    else if h : bits.take 3 = [true, false, true] then
      match decodeFormula? (bits.drop 3) with
      | some (f1, rest) =>
        match decodeFormula? rest with
        | some (f2, rest') => some (.iff f1 f2, rest')
        | none => none
      | none => none
    else
      none

theorem decodeNat?_encodeNat (n : Nat) : decodeNat? (encodeNat n) = some (n, []) := by
  induction n with
  | zero => simp [decodeNat?, encodeNat]
  | succ n ih => simp [decodeNat?, encodeNat, ih]

theorem decodeNat?_suffix (n : Nat) (rest : Bitstring) :
    decodeNat? (encodeNat n ++ rest) = some (n, rest) := by
  induction n with
  | zero => simp [decodeNat?, encodeNat]
  | succ n ih => simp [decodeNat?, encodeNat, ih, List.append_assoc]

private theorem take_prefix3 (p xs rest : Bitstring) (h : len p = 3) :
    List.take 3 (p ++ xs ++ rest) = p := by
  rw [len_eq] at h
  rw [List.append_assoc, List.take_append, h, Nat.sub_self, List.take_zero, List.append_nil]
  rw [← h, List.take_length]

private theorem take_prefix2 (p xs rest : Bitstring) (h : len p = 2) :
    List.take 2 (p ++ xs ++ rest) = p := by
  rw [len_eq] at h
  rw [List.append_assoc, List.take_append, h, Nat.sub_self, List.take_zero, List.append_nil]
  rw [← h, List.take_length]

@[simp] theorem take_termTag3 (t : Term) (mid rest : Bitstring) :
    List.take 3 (termTag t ++ mid ++ rest) = termTag t :=
  take_prefix3 (termTag t) mid rest (len_termTag t)

@[simp] theorem take_relationTag2 (r : Relation) (mid rest : Bitstring) :
    List.take 2 (relationTag r ++ mid ++ rest) = relationTag r :=
  take_prefix2 (relationTag r) mid rest (len_relationTag r)

@[simp] theorem take_formulaTag3 (f : Formula) (mid rest : Bitstring) :
    List.take 3 (formulaTag f ++ mid ++ rest) = formulaTag f :=
  take_prefix3 (formulaTag f) mid rest (len_formulaTag f)

private theorem take_serializeTerm_prefix3 (t : Term) (rest : Bitstring) :
    List.take 3 (serializeTerm t ++ rest) = termTag t := by
  cases t with
  | var n => simp [serializeTerm, termTag, take_prefix3, len_termTag, List.append_assoc]
  | empty => simp [serializeTerm, termTag, take_prefix3, len_termTag]
  | union t1 t2 => simp [serializeTerm, termTag, take_prefix3, len_termTag, List.append_assoc]
  | inter t1 t2 => simp [serializeTerm, termTag, take_prefix3, len_termTag, List.append_assoc]
  | diff t1 t2 => simp [serializeTerm, termTag, take_prefix3, len_termTag, List.append_assoc]

private theorem take_serializeRelation_prefix2 (r : Relation) (rest : Bitstring) :
    List.take 2 (serializeRelation r ++ rest) = relationTag r := by
  cases r with
  | mem t1 t2 | not_mem t1 t2 | eq t1 t2 | neq t1 t2 =>
    simp [serializeRelation, relationTag, take_prefix2, len_relationTag, List.append_assoc]

private theorem take_serializeFormula_prefix3 (f : Formula) (rest : Bitstring) :
    List.take 3 (serializeFormula f ++ rest) = formulaTag f := by
  cases f with
  | rel r => simp [serializeFormula, formulaTag, take_prefix3, len_formulaTag, List.append_assoc]
  | not f => simp [serializeFormula, formulaTag, take_prefix3, len_formulaTag, List.append_assoc]
  | and f1 f2 | or f1 f2 | imp f1 f2 | iff f1 f2 =>
    simp [serializeFormula, formulaTag, take_prefix3, len_formulaTag, List.append_assoc]

theorem decodeTerm?_suffix (t : Term) (rest : Bitstring) :
    decodeTerm? (serializeTerm t ++ rest) = some (t, rest) := by
  sorry

theorem decodeTerm?_serializeTerm (t : Term) :
    decodeTerm? (serializeTerm t) = some (t, []) := by
  simpa [List.append_nil] using decodeTerm?_suffix t []

theorem decodeRelation?_suffix (r : Relation) (rest : Bitstring) :
    decodeRelation? (serializeRelation r ++ rest) = some (r, rest) := by
  sorry

theorem decodeRelation?_serializeRelation (r : Relation) :
    decodeRelation? (serializeRelation r) = some (r, []) := by
  simpa [List.append_nil] using decodeRelation?_suffix r []

theorem decodeFormula?_suffix (f : Formula) (rest : Bitstring) :
    decodeFormula? (serializeFormula f ++ rest) = some (f, rest) := by
  sorry

theorem decodeFormula?_serializeFormula (f : Formula) :
    decodeFormula? (serializeFormula f) = some (f, []) := by
  simpa [List.append_nil] using decodeFormula?_suffix f []

end MLS
