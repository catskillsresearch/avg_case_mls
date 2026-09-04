import AvgCaseMls.Section3.Hypergraph
import AvgCaseMls.Section3.Lemma5Semantics
import AvgCaseMls.Section3.Unsatisfiability

/-!
# Forgetting signs in the random ordinary-CNF model

The unsigned projection has constant fibers of size `2^(k*m)`.  Consequently,
every event depending only on the ordered variable sets has exactly the same
probability in the signed and unsigned models.
-/

namespace AvgCaseMls.Section3

open scoped BigOperators

/-- Forget the signs of an ordered ordinary CNF, retaining edge order. -/
def unsignedProjection (F : OrdinaryCNF n m k) :
    OrderedKUniformHypergraph n m k :=
  fun i => (F i).1

@[simp] theorem unsignedProjection_toHypergraph
    (F : OrdinaryCNF n m k) :
    (unsignedProjection F).toHypergraph = clauseHypergraph F := by
  rfl

theorem eraseOrdinary_basedOn_projection (F : OrdinaryCNF n m k) :
    ClauseFamilyBasedOn (unsignedProjection F).toHypergraph
      (eraseOrdinary F) := by
  intro i
  refine ⟨(F i).lits_isOrdinary.2, ?_⟩
  ext x
  simp only [clauseVarSet, Finset.mem_image, eraseOrdinary,
    OrderedKUniformHypergraph.toHypergraph, unsignedProjection]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (F i).mem_varSet_iff l.1 |>.2 ⟨l, hl, rfl⟩
  · intro hx
    rcases ((F i).mem_varSet_iff x).1 hx with ⟨l, hl, hlx⟩
    exact ⟨l, hl, hlx⟩

private def splitOrdinaryCNF :
    OrdinaryCNF n m k ≃
      Sigma fun G : OrderedKUniformHypergraph n m k =>
        ∀ i, (G i).val → Bool where
  toFun F := ⟨unsignedProjection F, fun i => (F i).2⟩
  invFun p := fun i => ⟨p.1 i, p.2 i⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def projectionEventEquiv (E : Finset (OrderedKUniformHypergraph n m k)) :
    {F : OrdinaryCNF n m k //
      F ∈ Finset.univ.filter (fun G => unsignedProjection G ∈ E)} ≃
      Sigma fun G : {G // G ∈ E} => ∀ i, (G.val i).val → Bool where
  toFun F :=
    ⟨⟨unsignedProjection F.val, (Finset.mem_filter.mp F.property).2⟩,
      fun i => (F.val i).2⟩
  invFun p := ⟨fun i => ⟨p.1.val i, p.2 i⟩, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (fun i => p.1.val i) ∈ E
    exact p.1.property⟩
  left_inv F := Subtype.ext rfl
  right_inv p := Sigma.ext (Subtype.ext rfl) (by rfl)

theorem projectionEvent_card
    (E : Finset (OrderedKUniformHypergraph n m k)) :
    (Finset.univ.filter fun F : OrdinaryCNF n m k =>
      unsignedProjection F ∈ E).card =
      E.card * (2 ^ k) ^ m := by
  classical
  rw [← Fintype.card_coe,
    Fintype.card_congr (projectionEventEquiv E), Fintype.card_sigma]
  have hfiber : ∀ G : {G // G ∈ E},
      Fintype.card (∀ i, (G.val i).val → Bool) = (2 ^ k) ^ m := by
    intro G
    rw [Fintype.card_pi]
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    have hfun :
        (fun i : Fin m => 2 ^ (G.val i).val.card) =
          fun _ => 2 ^ k := by
      funext i
      rw [(G.val i).property]
    rw [hfun]
    simp
  simp_rw [hfiber]
  simp

/-- Exact transfer of an unsigned event to the signed random-CNF model. -/
theorem projection_event_probability
    (hk : k ≤ n) (m : Nat)
    (E : Finset (OrderedKUniformHypergraph n m k)) :
    (randomCNFOfLE n m k hk).eventProb
        {F | unsignedProjection F ∈ E} =
      (randomOrderedKUniformHypergraphOfLE n m k hk).eventProb (E : Set _) := by
  letI : Nonempty (OrdinaryClause n k) := ordinaryClause_nonempty hk
  let C := positiveOrdinaryClause hk
  letI : Nonempty (ClauseVariables n k) := ⟨C.1⟩
  change (FinitePMF.uniform (OrdinaryCNF n m k)).eventProb
      {F | unsignedProjection F ∈ E} =
    (FinitePMF.uniform (OrderedKUniformHypergraph n m k)).eventProb (E : Set _)
  rw [show ({F | unsignedProjection F ∈ E} : Set (OrdinaryCNF n m k)) =
      (Finset.univ.filter fun F => unsignedProjection F ∈ E : Finset _) by
        ext F
        simp,
    FinitePMF.uniform_eventProb, FinitePMF.uniform_eventProb,
    projectionEvent_card, ordinaryCNF_cardinality,
    orderedKUniformHypergraph_cardinality]
  have hchoose : (0 : ℝ) < n.choose k := by
    exact_mod_cast Nat.choose_pos hk
  push_cast
  rw [mul_pow]
  field_simp

noncomputable def denseProjectedEvent
    (c k : Nat) (E : ∀ r, Set (OrderedKUniformHypergraph
      (r + k) (c * (r + k)) k)) (r : Nat) :
    Set (OrdinaryCNF (r + k) (c * (r + k)) k) :=
  {F | unsignedProjection F ∈ E r}

theorem dense_projection_withHighProbability
    (c k : Nat)
    (E : ∀ r, Set (OrderedKUniformHypergraph
      (r + k) (c * (r + k)) k))
    (hE : WithHighProbability (denseRandomHypergraph c k) E) :
    WithHighProbability (denseRandomCNF c k)
      (denseProjectedEvent c k E) := by
  have heq : ∀ r,
      (denseRandomCNF c k r).eventProb (denseProjectedEvent c k E r) =
        (denseRandomHypergraph c k r).eventProb (E r) := by
    intro r
    classical
    let Ef : Finset (OrderedKUniformHypergraph
        (r + k) (c * (r + k)) k) := Finset.univ.filter (· ∈ E r)
    simpa [denseRandomCNF, denseRandomHypergraph, denseProjectedEvent, Ef]
      using projection_event_probability (Nat.le_add_left k r)
        (c * (r + k)) Ef
  unfold WithHighProbability at hE ⊢
  convert hE using 1
  funext r
  exact heq r

end AvgCaseMls.Section3
