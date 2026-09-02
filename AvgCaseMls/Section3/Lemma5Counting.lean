import AvgCaseMls.Section3.Lemma5Semantics

/-!
# CS87 Lemma 5: finite counting

This file contains the assignment injection behind (6.5), together with the
set-intersection estimate used to pass from `D(S)` to `S` before (6.4).
-/

namespace AvgCaseMls.Section3

noncomputable def badPartialAssignments
    (D : Finset (Fin n)) (C : Clause n) :
    Finset (PartialAssignment D) := by
  classical
  exact Finset.univ.filter fun f => ¬ PartialSatisfiesClause f C

theorem partial_unsat_agree_on_clauseVar
    {D : Finset (Fin n)} {C : Clause n}
    (_hord : IsOrdinaryClause C)
    {f g : PartialAssignment D}
    (hf : ¬ PartialSatisfiesClause f C)
    (hg : ¬ PartialSatisfiesClause g C)
    {x : Fin n} (hxD : x ∈ D) (hxC : x ∈ clauseVarSet C) :
    f ⟨x, hxD⟩ = g ⟨x, hxD⟩ := by
  rcases (mem_clauseVarSet_iff C x).mp hxC with ⟨l, hl, hlx⟩
  rcases l with ⟨y, sign⟩
  simp only [Literal.varOf] at hlx
  subst y
  have hffalse :
      (if sign then f ⟨x, hxD⟩ else !(f ⟨x, hxD⟩)) = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact hf ⟨(x, sign), hl, hxD, htrue⟩
  have hgfalse :
      (if sign then g ⟨x, hxD⟩ else !(g ⟨x, hxD⟩)) = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact hg ⟨(x, sign), hl, hxD, htrue⟩
  cases sign <;> simp_all

/-- Assignment injection in (6.5): after fixing that a partial assignment
does not satisfy `C`, values on `D ∩ E(C)` are forced, leaving at most
`2^(|D|-|D∩E(C)|)` choices. -/
theorem badPartialAssignments_card_le
    (D : Finset (Fin n)) (C : Clause n)
    (_hord : IsOrdinaryClause C) :
    (badPartialAssignments D C).card ≤
      2 ^ (D.card - (D ∩ clauseVarSet C).card) := by
  classical
  let B := {f // f ∈ badPartialAssignments D C}
  let R := D \ clauseVarSet C
  let restrict : B → (R → Bool) := fun f x =>
    f.val ⟨x.val, (Finset.mem_sdiff.mp x.property).1⟩
  have hinj : Function.Injective restrict := by
    intro f g heq
    apply Subtype.ext
    funext x
    by_cases hx : x.val ∈ clauseVarSet C
    · exact partial_unsat_agree_on_clauseVar _hord
        (by simpa [badPartialAssignments] using
          (Finset.mem_filter.mp f.property).2)
        (by simpa [badPartialAssignments] using
          (Finset.mem_filter.mp g.property).2)
        x.property hx
    · have hr : (⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩ : R) =
          ⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩ := rfl
      have := congrFun heq
        (⟨x.val, Finset.mem_sdiff.mpr ⟨x.property, hx⟩⟩ : R)
      exact this
  have hcard := Fintype.card_le_of_injective restrict hinj
  have hBcard : Fintype.card B = (badPartialAssignments D C).card := by
    dsimp [B]
    exact Fintype.card_coe _
  have hfunCard : Fintype.card (R → Bool) = 2 ^ R.card := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  have hRcard :
      R.card = D.card - (D ∩ clauseVarSet C).card := by
    dsimp [R]
    rw [Finset.card_sdiff, Finset.inter_comm]
  rw [hBcard, hfunCard, hRcard] at hcard
  exact hcard

/-- The elementary implication immediately before (6.4):
`D ⊆ S` and at most `t` points of `S` were deleted, so a small intersection
with `D` forces a small intersection with `S`. -/
theorem card_inter_le_of_domain_inter_le
    {D S E : Finset α} [DecidableEq α]
    (_hDS : D ⊆ S) (hdelete : (S \ D).card ≤ t)
    (hinter : (D ∩ E).card ≤ r) :
    (S ∩ E).card ≤ r + t := by
  have hsub : S ∩ E ⊆ (D ∩ E) ∪ (S \ D) := by
    intro x hx
    have hx' := Finset.mem_inter.mp hx
    by_cases hxD : x ∈ D
    · exact Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hxD, hx'.2⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hx'.1, hxD⟩)
  calc
    (S ∩ E).card ≤ ((D ∩ E) ∪ (S \ D)).card :=
      Finset.card_le_card hsub
    _ ≤ (D ∩ E).card + (S \ D).card := Finset.card_union_le _ _
    _ ≤ r + t := Nat.add_le_add hinter hdelete

end AvgCaseMls.Section3
