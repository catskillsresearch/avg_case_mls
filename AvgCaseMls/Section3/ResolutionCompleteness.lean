import AvgCaseMls.Section3.Lemma5Semantics
import AvgCaseMls.Section3.Unsatisfiability

/-!
# Finite completeness of resolution

The paper uses resolution complexity only for unsatisfiable ordinary CNFs.
This file supplies the previously missing converse to resolution soundness:
every finite unsatisfiable family of ordinary clauses has a refutation in the
resolution calculus used by Section 3.
-/

namespace AvgCaseMls.Section3

theorem ResolutionProof.append {F : Fin m → Clause n}
    {cs ds : List (Clause n)}
    (hcs : ResolutionProof F cs) (hds : ResolutionProof F ds) :
    ResolutionProof F (cs ++ ds) := by
  induction hds with
  | nil => simpa using hcs
  | input ds h i ih =>
      simpa [List.append_assoc] using ResolutionProof.input (cs ++ ds) ih i
  | resolve ds h A B hA hB C hC ih =>
      simpa [List.append_assoc] using
        ResolutionProof.resolve (cs ++ ds) ih A B
          (List.mem_append_right cs hA) (List.mem_append_right cs hB) C hC

def ResolutionDerives (F : Fin m → Clause n) (C : Clause n) : Prop :=
  ∃ cs, ResolutionProof F cs ∧ C ∈ cs

theorem resolutionDerives_input (F : Fin m → Clause n) (i : Fin m) :
    ResolutionDerives F (F i) := by
  exact ⟨[F i], ResolutionProof.input [] ResolutionProof.nil i, by simp⟩

theorem resolutionDerives_resolvent
    {F : Fin m → Clause n} {A B C : Clause n}
    (hA : ResolutionDerives F A) (hB : ResolutionDerives F B)
    (hC : IsResolvent C A B) :
    ResolutionDerives F C := by
  rcases hA with ⟨cs, hcs, hAcs⟩
  rcases hB with ⟨ds, hds, hBds⟩
  let es := (cs ++ ds) ++ [C]
  refine ⟨es, ?_, by simp [es]⟩
  apply ResolutionProof.resolve (cs ++ ds) (hcs.append hds) A B
  · exact List.mem_append_left ds hAcs
  · exact List.mem_append_right cs hBds
  · exact hC

/-- The clause containing, for each variable in `D`, the unique literal
falsified by the partial assignment. -/
def partialBlockingClause {D : Finset (Fin n)}
    (f : PartialAssignment D) : Clause n :=
  D.attach.image fun x => (x.val, !(f x))

theorem mem_partialBlockingClause_iff
    {D : Finset (Fin n)} (f : PartialAssignment D) (l : Literal n) :
    l ∈ partialBlockingClause f ↔
      ∃ h : l.varOf ∈ D, l.2 = !(f ⟨l.1, h⟩) := by
  constructor
  · intro hl
    rcases Finset.mem_image.mp hl with ⟨x, _, hx⟩
    subst l
    exact ⟨x.property, rfl⟩
  · rintro ⟨h, hs⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨l.1, h⟩, Finset.mem_attach _ _, ?_⟩
    ext
    · rfl
    · exact hs.symm

private def extendPartial {D : Finset (Fin n)}
    (f : PartialAssignment D) (x : Fin n) (b : Bool) :
    PartialAssignment (insert x D) :=
  fun y => if h : y.val = x then b else
    f ⟨y.val, by
      rcases Finset.mem_insert.mp y.property with hy | hy
      · exact absurd hy h
      · exact hy⟩

@[simp] private theorem extendPartial_at {D : Finset (Fin n)}
    (f : PartialAssignment D) (x : Fin n) (b : Bool)
    (hx : x ∉ D) :
    extendPartial f x b ⟨x, Finset.mem_insert_self x D⟩ = b := by
  simp [extendPartial]

private theorem blocking_erase_subset
    {D : Finset (Fin n)} (f : PartialAssignment D)
    (x : Fin n) (hx : x ∉ D) (b : Bool) :
    partialBlockingClause (extendPartial f x b) \
        {(x, !b)} ⊆ partialBlockingClause f := by
  intro l hl
  have hlblock := (Finset.mem_sdiff.mp hl).1
  have hlne := (Finset.mem_sdiff.mp hl).2
  rcases (mem_partialBlockingClause_iff (extendPartial f x b) l).1 hlblock with
    ⟨hlD, hsign⟩
  have hlx : l.1 ≠ x := by
    intro heq
    subst x
    have hvalue :
        extendPartial f l.1 b ⟨l.1, hlD⟩ = b := by
      simp [extendPartial]
    apply hlne
    simp only [Finset.mem_singleton]
    ext
    · rfl
    · simpa [hvalue] using hsign
  have hlold : l.1 ∈ D := by
    rcases Finset.mem_insert.mp hlD with h | h
    · exact absurd h hlx
    · exact h
  apply (mem_partialBlockingClause_iff f l).2
  refine ⟨hlold, ?_⟩
  simpa [extendPartial, hlx] using hsign

private theorem pivot_mem_blocking
    {D : Finset (Fin n)} (f : PartialAssignment D)
    (x : Fin n) (hx : x ∉ D) (b : Bool) :
    (x, !b) ∈ partialBlockingClause (extendPartial f x b) := by
  apply (mem_partialBlockingClause_iff (extendPartial f x b) _).2
  exact ⟨Finset.mem_insert_self x D, by simp [extendPartial]⟩

private theorem input_subset_full_blocking
    {F : Fin m → Clause n} (hordinary : ∀ i, IsOrdinaryClause (F i))
    (f : PartialAssignment (Finset.univ : Finset (Fin n)))
    (i : Fin m)
    (hfalse : ¬ SatisfiesClause
      (fun x => f ⟨x, Finset.mem_univ x⟩) (F i)) :
    F i ⊆ partialBlockingClause f := by
  intro l hl
  apply (mem_partialBlockingClause_iff f l).2
  refine ⟨Finset.mem_univ _, ?_⟩
  have heval :
      evalLiteral (fun x => f ⟨x, Finset.mem_univ x⟩) l = false := by
    cases h : evalLiteral (fun x => f ⟨x, Finset.mem_univ x⟩) l
    · rfl
    · exact absurd ⟨l, hl, h⟩ hfalse
  simpa using (evalLiteral_eq_false_iff_sign.mp heval)

private theorem resolution_complete_aux
    {F : Fin m → Clause n} (hordinary : ∀ i, IsOrdinaryClause (F i))
    (D : Finset (Fin n)) (f : PartialAssignment D)
    (hunsat : ∀ a : Assignment n, ExtendsPartial a f → ¬ SatisfiesCNF a F) :
    ∃ C, ResolutionDerives F C ∧ C ⊆ partialBlockingClause f := by
  classical
  induction hq : ((Finset.univ : Finset (Fin n)) \ D).card using
      Nat.strong_induction_on generalizing D with
  | h q ih =>
      by_cases hfull : D = Finset.univ
      · subst D
        let a : Assignment n := fun x => f ⟨x, Finset.mem_univ x⟩
        have hnall : ¬ ∀ i, SatisfiesClause a (F i) := hunsat a (by
          intro x
          rfl)
        push_neg at hnall
        rcases hnall with ⟨i, hi⟩
        exact ⟨F i, resolutionDerives_input F i,
          input_subset_full_blocking hordinary f i hi⟩
      · have hcomp : ((Finset.univ : Finset (Fin n)) \ D).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro he
          apply hfull
          exact Finset.eq_univ_of_forall fun x => by
            by_contra hx
            have : x ∈ (Finset.univ : Finset (Fin n)) \ D := by simp [hx]
            simpa [he] using this
        let x := hcomp.choose
        have hxcomp := hcomp.choose_spec
        have hxD : x ∉ D := (Finset.mem_sdiff.mp hxcomp).2
        let f0 := extendPartial f x false
        let f1 := extendPartial f x true
        have hcardlt :
            ((Finset.univ : Finset (Fin n)) \ insert x D).card < q := by
          rw [← hq]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨?_, ?_⟩
          · intro y hy
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hy ⊢
            exact fun h => hy (Finset.mem_insert_of_mem h)
          · intro heq
            have hxnew :
                x ∈ (Finset.univ : Finset (Fin n)) \ insert x D := heq ▸ hxcomp
            simpa using hxnew
        have hu0 : ∀ a : Assignment n, ExtendsPartial a f0 →
            ¬ SatisfiesCNF a F := by
          intro a ha
          apply hunsat a
          intro y
          have hyne : y.val ≠ x := fun heq => hxD (heq ▸ y.property)
          simpa [f0, extendPartial, hyne] using
            ha ⟨y.val, Finset.mem_insert_of_mem y.property⟩
        have hu1 : ∀ a : Assignment n, ExtendsPartial a f1 →
            ¬ SatisfiesCNF a F := by
          intro a ha
          apply hunsat a
          intro y
          have hyne : y.val ≠ x := fun heq => hxD (heq ▸ y.property)
          simpa [f1, extendPartial, hyne] using
            ha ⟨y.val, Finset.mem_insert_of_mem y.property⟩
        rcases ih _ hcardlt (insert x D) f0 hu0 rfl with
          ⟨C0, hderive0, hC0⟩
        rcases ih _ hcardlt (insert x D) f1 hu1 rfl with
          ⟨C1, hderive1, hC1⟩
        by_cases hp : Literal.pos x ∈ C0
        · by_cases hn : Literal.neg x ∈ C1
          · let R := resolvent C0 C1 x
            refine ⟨R, resolutionDerives_resolvent hderive0 hderive1
              ⟨x, hp, hn, rfl⟩, ?_⟩
            intro l hl
            rcases Finset.mem_union.mp hl with hl | hl
            · exact blocking_erase_subset f x hxD false
                (Finset.mem_sdiff.mpr ⟨hC0 (Finset.mem_of_mem_erase hl), by
                  simpa [Literal.pos] using (Finset.ne_of_mem_erase hl)⟩)
            · exact blocking_erase_subset f x hxD true
                (Finset.mem_sdiff.mpr ⟨hC1 (Finset.mem_of_mem_erase hl), by
                  simpa [Literal.neg] using (Finset.ne_of_mem_erase hl)⟩)
          · refine ⟨C1, hderive1, ?_⟩
            intro l hl
            exact blocking_erase_subset f x hxD true
              (Finset.mem_sdiff.mpr ⟨hC1 hl, by
                intro hlone
                apply hn
                have heq : l = Literal.neg x := by
                  simpa [Literal.neg] using hlone
                rwa [← heq]⟩)
        · refine ⟨C0, hderive0, ?_⟩
          intro l hl
          exact blocking_erase_subset f x hxD false
            (Finset.mem_sdiff.mpr ⟨hC0 hl, by
              intro hlone
              apply hp
              have heq : l = Literal.pos x := by
                simpa [Literal.pos] using hlone
              rwa [← heq]⟩)

/-- Completeness of finite resolution for ordinary clause families. -/
theorem resolution_complete
    {F : Fin m → Clause n}
    (hordinary : ∀ i, IsOrdinaryClause (F i))
    (hunsat : ¬ Satisfiable F) :
    ∃ cs, ResolutionRefutation F cs := by
  classical
  let f : PartialAssignment (∅ : Finset (Fin n)) := fun x => nomatch x.property
  have hu : ∀ a : Assignment n, ExtendsPartial a f →
      ¬ SatisfiesCNF a F := by
    intro a _ ha
    exact hunsat ⟨a, ha⟩
  rcases resolution_complete_aux hordinary ∅ f hu with
    ⟨C, ⟨cs, hproof, hmem⟩, hC⟩
  have hCe : C = ∅ := Finset.subset_empty.mp (by
    simpa [partialBlockingClause] using hC)
  subst C
  exact ⟨cs, hproof, hmem⟩

end AvgCaseMls.Section3
