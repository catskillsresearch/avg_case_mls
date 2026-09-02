import AvgCaseMls.Section3.Lemma5Counting

/-!
# CS87 Lemma 5: the minimal-support flip argument

This file formalizes the semantic implication relation used in §6 and the
boundary-variable argument (6.7).
-/

namespace AvgCaseMls.Section3

def ImpliesSubject {D : Finset (Fin n)}
    (F : Fin m → Clause n) (f : PartialAssignment D)
    (I : Finset (Fin m)) (C : Clause n) : Prop :=
  ∀ g : Assignment n, ExtendsPartial g f →
    SatisfiesIndexedFamily g F I → SatisfiesClause g C

def InclusionMinimalImpliesSubject
    {D : Finset (Fin n)} (F : Fin m → Clause n) (f : PartialAssignment D)
    (I : Finset (Fin m)) (C : Clause n) : Prop :=
  ImpliesSubject F f I C ∧
    ∀ i ∈ I, ¬ ImpliesSubject F f (I.erase i) C

def flipVariable (g : Assignment n) (x : Fin n) : Assignment n :=
  fun y => if y = x then !(g y) else g y

@[simp] theorem flipVariable_at (g : Assignment n) (x : Fin n) :
    flipVariable g x x = !(g x) := by
  simp [flipVariable]

theorem flipVariable_of_ne (g : Assignment n) {x y : Fin n} (h : y ≠ x) :
    flipVariable g x y = g y := by
  simp [flipVariable, h]

theorem flipVariable_extends
    {D : Finset (Fin n)} {f : PartialAssignment D}
    {g : Assignment n} (hg : ExtendsPartial g f)
    {x : Fin n} (hxD : x ∉ D) :
    ExtendsPartial (flipVariable g x) f := by
  intro y
  rw [flipVariable_of_ne]
  · exact hg y
  · intro h
    subst x
    exact hxD y.property

theorem evalLiteral_flip_of_other_var
    (g : Assignment n) (x : Fin n) {l : Literal n}
    (h : l.varOf ≠ x) :
    evalLiteral (flipVariable g x) l = evalLiteral g l := by
  rcases l with ⟨y, sign⟩
  simp only [Literal.varOf] at h
  simp [evalLiteral, flipVariable_of_ne g h]

theorem satisfiesClause_flip_iff_of_not_mem_varSet
    (g : Assignment n) (x : Fin n) (C : Clause n)
    (hx : x ∉ clauseVarSet C) :
    SatisfiesClause (flipVariable g x) C ↔ SatisfiesClause g C := by
  constructor
  · rintro ⟨l, hl, heval⟩
    refine ⟨l, hl, ?_⟩
    rw [evalLiteral_flip_of_other_var] at heval
    · exact heval
    · intro heq
      exact hx ((mem_clauseVarSet_iff C x).mpr ⟨l, hl, heq⟩)
  · rintro ⟨l, hl, heval⟩
    refine ⟨l, hl, ?_⟩
    rw [evalLiteral_flip_of_other_var]
    · exact heval
    · intro heq
      exact hx ((mem_clauseVarSet_iff C x).mpr ⟨l, hl, heq⟩)

theorem flip_satisfies_ordinary_clause
    {C : Clause n} (_hord : IsOrdinaryClause C)
    {g : Assignment n} (hnot : ¬ SatisfiesClause g C)
    {x : Fin n} (hx : x ∈ clauseVarSet C) :
    SatisfiesClause (flipVariable g x) C := by
  rcases (mem_clauseVarSet_iff C x).mp hx with ⟨l, hl, hlx⟩
  refine ⟨l, hl, ?_⟩
  have hfalse : evalLiteral g l = false := by
    cases hval : evalLiteral g l
    · rfl
    · exact absurd ⟨l, hl, hval⟩ hnot
  rcases l with ⟨y, sign⟩
  simp only [Literal.varOf] at hlx
  subst y
  cases sign <;> simp [evalLiteral, flipVariable] at hfalse ⊢ <;>
    assumption

theorem satisfiesIndexedFamily_flip_of_unique_edge
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F)
    {I : Finset (Fin m)} {i : Fin m} (_hiI : i ∈ I)
    {x : Fin n}
    (hunique : I.filter (fun j => x ∈ H.edge j) = {i})
    {g : Assignment n}
    (hrest : SatisfiesIndexedFamily g F (I.erase i))
    (hnoti : ¬ SatisfiesClause g (F i)) :
    SatisfiesIndexedFamily (flipVariable g x) F I := by
  intro j hjI
  by_cases hji : j = i
  · subst j
    apply flip_satisfies_ordinary_clause (hbased i).1 hnoti
    rw [(hbased i).2]
    have : i ∈ I.filter fun j => x ∈ H.edge j := by
      rw [hunique]
      simp
    exact (Finset.mem_filter.mp this).2
  · have hxnot : x ∉ H.edge j := by
      intro hxj
      have hjfilter : j ∈ I.filter fun z => x ∈ H.edge z :=
        Finset.mem_filter.mpr ⟨hjI, hxj⟩
      rw [hunique] at hjfilter
      exact hji (Finset.mem_singleton.mp hjfilter)
    rw [satisfiesClause_flip_iff_of_not_mem_varSet]
    · exact hrest j (Finset.mem_erase.mpr ⟨hji, hjI⟩)
    · rwa [(hbased j).2]

/-- Equation (6.7): every boundary variable outside the partial-assignment
domain occurs in the minimally implied clause. -/
theorem boundary_diff_subset_implied_clause
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F)
    {D : Finset (Fin n)} (f : PartialAssignment D)
    {I : Finset (Fin m)} {C : Clause n}
    (hmin : InclusionMinimalImpliesSubject F f I C) :
    H.boundary I \ D ⊆ clauseVarSet C := by
  intro x hx
  have hxboundary := (Finset.mem_sdiff.mp hx).1
  have hxD := (Finset.mem_sdiff.mp hx).2
  have hdegree := (H.mem_boundary I x).mp hxboundary
  simp only [Hypergraph.degreeIn, Finset.card_eq_one] at hdegree
  rcases hdegree with ⟨i, hunique⟩
  have hiFilter : i ∈ I.filter (fun j => x ∈ H.edge j) := by
    rw [hunique]
    simp
  have hiI := (Finset.mem_filter.mp hiFilter).1
  have hnotImplies := hmin.2 i hiI
  rw [ImpliesSubject] at hnotImplies
  have hexists :
      ∃ g : Assignment n, ExtendsPartial g f ∧
        SatisfiesIndexedFamily g F (I.erase i) ∧
          ¬ SatisfiesClause g C := by
    by_contra h
    apply hnotImplies
    intro g hgext hgrest
    by_contra hgnotC
    exact h ⟨g, hgext, hgrest, hgnotC⟩
  rcases hexists with ⟨g, hgext, hgrest, hgnotC⟩
  have hgnoti : ¬ SatisfiesClause g (F i) := by
    intro hgi
    apply hgnotC
    apply hmin.1 g hgext
    intro j hjI
    by_cases hji : j = i
    · simpa [hji] using hgi
    · exact hgrest j (Finset.mem_erase.mpr ⟨hji, hjI⟩)
  have hflipFamily :
      SatisfiesIndexedFamily (flipVariable g x) F I :=
    satisfiesIndexedFamily_flip_of_unique_edge hbased hiI hunique
      hgrest hgnoti
  have hflipC : SatisfiesClause (flipVariable g x) C :=
    hmin.1 (flipVariable g x)
      (flipVariable_extends hgext hxD) hflipFamily
  by_contra hxC
  exact hgnotC
    ((satisfiesClause_flip_iff_of_not_mem_varSet g x C hxC).mp hflipC)

theorem impliesSubject_mono
    {F : Fin m → Clause n} {D : Finset (Fin n)}
    (f : PartialAssignment D) {I J : Finset (Fin m)} {C : Clause n}
    (hIJ : I ⊆ J) (hI : ImpliesSubject F f I C) :
    ImpliesSubject F f J C := by
  intro g hg hJ
  exact hI g hg (fun i hi => hJ i (hIJ hi))

theorem input_impliesSubject
    {F : Fin m → Clause n} {D : Finset (Fin n)}
    (f : PartialAssignment D) (i : Fin m) :
    ImpliesSubject F f {i} (F i) := by
  intro g _ hg
  exact hg i (by simp)

theorem union_implies_resolvent
    {F : Fin m → Clause n} {D : Finset (Fin n)}
    (f : PartialAssignment D)
    {I J : Finset (Fin m)} {A B C : Clause n}
    (hI : ImpliesSubject F f I A) (hJ : ImpliesSubject F f J B)
    (hres : IsResolvent C A B) :
    ImpliesSubject F f (I ∪ J) C := by
  intro g hg hIJ
  apply resolution_sound
  · exact hI g hg (fun i hi => hIJ i (Finset.mem_union_left _ hi))
  · exact hJ g hg (fun i hi => hIJ i (Finset.mem_union_right _ hi))
  · exact hres

theorem exists_inclusionMinimal_implying_subset
    {F : Fin m → Clause n} {D : Finset (Fin n)}
    (f : PartialAssignment D) {I : Finset (Fin m)} {C : Clause n}
    (hI : ImpliesSubject F f I C) :
    ∃ J ⊆ I, InclusionMinimalImpliesSubject F f J C := by
  classical
  let good := I.powerset.filter fun J => ImpliesSubject F f J C
  have hgood : good.Nonempty := ⟨I, by simp [good, hI]⟩
  rcases Finset.exists_min_image good Finset.card hgood with
    ⟨J, hJgood, hmin⟩
  have hJI : J ⊆ I :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hJgood).1
  have hJimply : ImpliesSubject F f J C :=
    (Finset.mem_filter.mp hJgood).2
  refine ⟨J, hJI, hJimply, ?_⟩
  intro i hiJ himply
  have heraseSub : J.erase i ⊆ I :=
    (Finset.erase_subset _ _).trans hJI
  have heraseGood : J.erase i ∈ good :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr heraseSub, himply⟩
  have hcardMin := hmin (J.erase i) heraseGood
  exact (Nat.not_lt_of_ge hcardMin) (Finset.card_erase_lt_of_mem hiJ)

def IsComplexSubject
    {D : Finset (Fin n)} (F : Fin m → Clause n)
    (f : PartialAssignment D) (a : ℝ) (C : Clause n) : Prop :=
  ¬ ∃ I : Finset (Fin m), (I.card : ℝ) ≤ a * n / 2 ∧
      ImpliesSubject F f I C

theorem complex_not_partialSatisfies
    {F : Fin m → Clause n} {D : Finset (Fin n)}
    (f : PartialAssignment D) {a : ℝ} (ha : 0 ≤ a) {C : Clause n}
    (hcomplex : IsComplexSubject F f a C) :
    ¬ PartialSatisfiesClause f C := by
  intro hsat
  apply hcomplex
  refine ⟨∅, ?_, ?_⟩
  · simp
    positivity
  intro g hg _
  exact satisfiesClause_of_partialSatisfies f C hg hsat

/-- The quantitative content of (6.6), using (6.7). -/
theorem implied_clause_large_of_complex
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F) (hP : H.HasPropertyP a)
    {D : Finset (Fin n)} (f : PartialAssignment D)
    (hDsmall : (D.card : ℝ) ≤ a * n / 8)
    {I : Finset (Fin m)} {C : Clause n}
    (hIcard : (I.card : ℝ) ≤ a * n)
    (hIimply : ImpliesSubject F f I C)
    (hcomplex : IsComplexSubject F f a C) :
    a * n / 8 < (clauseVarSet C).card := by
  rcases exists_inclusionMinimal_implying_subset f hIimply with
    ⟨J, hJI, hJmin⟩
  have hJcard : (J.card : ℝ) ≤ a * n := by
    calc
      (J.card : ℝ) ≤ I.card := by
        exact_mod_cast Finset.card_le_card hJI
      _ ≤ a * n := hIcard
  have hJlarge : a * n / 2 < (J.card : ℝ) := by
    by_contra h
    apply hcomplex
    exact ⟨J, le_of_not_gt h, hJmin.1⟩
  have hboundary := hP J hJcard
  have hdiff :
      a * n / 8 < ((H.boundary J \ D).card : ℝ) := by
    have hpartNat :
        (H.boundary J \ D).card + (H.boundary J ∩ D).card =
          (H.boundary J).card := Finset.card_sdiff_add_card_inter _ _
    have hpart :
        ((H.boundary J \ D).card : ℝ) +
            ((H.boundary J ∩ D).card : ℝ) =
          ((H.boundary J).card : ℝ) := by exact_mod_cast hpartNat
    have hinterNat :
        (H.boundary J ∩ D).card ≤ D.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hinter :
        ((H.boundary J ∩ D).card : ℝ) ≤ D.card := by
      exact_mod_cast hinterNat
    nlinarith
  have hsub := boundary_diff_subset_implied_clause hbased f hJmin
  have hcardSub : (H.boundary J \ D).card ≤ (clauseVarSet C).card :=
    Finset.card_le_card hsub
  exact lt_of_lt_of_le hdiff (by exact_mod_cast hcardSub)

theorem empty_complex_of_specialDomain
    {F : Fin m → Clause n} {D : Finset (Fin n)}
    (f : PartialAssignment D) {a : ℝ}
    (hspecial : IsSpecialDomain F a D) :
    IsComplexSubject F f a (∅ : Clause n) := by
  rintro ⟨I, hIhalf, hIimply⟩
  have hI : (I.card : ℝ) ≤ a * n := by
    have hnonneg : 0 ≤ (I.card : ℝ) := by positivity
    nlinarith
  rcases hspecial f I hI with ⟨g, hgext, hgsat⟩
  exact not_satisfies_empty g (hIimply g hgext hgsat)

/-- CS87 (6.3)/(6.6): every refutation contains a clause not satisfied by
the special partial assignment and having more than `an/8` variables. -/
theorem resolutionRefutation_has_large_unsatisfied_clause
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F) (hP : H.HasPropertyP a)
    (ha : 0 ≤ a)
    (ha2 : 2 ≤ a * n)
    {D : Finset (Fin n)} (f : PartialAssignment D)
    (hspecial : IsSpecialDomain F a D)
    (hDsmall : (D.card : ℝ) ≤ a * n / 8)
    {cs : List (Clause n)} (href : ResolutionRefutation F cs) :
    ∃ C ∈ cs, ¬ PartialSatisfiesClause f C ∧
      a * n / 8 < (clauseVarSet C).card := by
  have hstep : ∀ {ds : List (Clause n)}, ResolutionProof F ds →
      (∃ C ∈ ds, IsComplexSubject F f a C) →
      ∃ C ∈ ds, ¬ PartialSatisfiesClause f C ∧
        a * n / 8 < (clauseVarSet C).card := by
    intro ds hp
    induction hp with
    | nil => simp
    | input ds hp i ih =>
        intro hex
        simp only [List.mem_append, List.mem_singleton] at hex ⊢
        rcases hex with ⟨C, hC | rfl, hc⟩
        · rcases ih ⟨C, hC, hc⟩ with ⟨K, hK, hu, hw⟩
          exact ⟨K, Or.inl hK, hu, hw⟩
        · exfalso
          apply hc
          refine ⟨{i}, ?_, input_impliesSubject f i⟩
          norm_num
          nlinarith
    | resolve ds hp A B hA hB R hres ih =>
        intro hex
        simp only [List.mem_append, List.mem_singleton] at hex ⊢
        rcases hex with ⟨K, hK | rfl, hcomplex⟩
        · rcases ih ⟨K, hK, hcomplex⟩ with ⟨L, hL, hu, hw⟩
          exact ⟨L, Or.inl hL, hu, hw⟩
        · by_cases hprev : ∃ K ∈ ds, IsComplexSubject F f a K
          · rcases ih hprev with ⟨L, hL, hu, hw⟩
            exact ⟨L, Or.inl hL, hu, hw⟩
          · have hAnon : ¬ IsComplexSubject F f a A := by
              intro h
              exact hprev ⟨A, hA, h⟩
            have hBnon : ¬ IsComplexSubject F f a B := by
              intro h
              exact hprev ⟨B, hB, h⟩
            rw [IsComplexSubject] at hAnon hBnon
            push Not at hAnon hBnon
            rcases hAnon with ⟨IA, hIAcard, hIA⟩
            rcases hBnon with ⟨IB, hIBcard, hIB⟩
            have hunionCard : (((IA ∪ IB).card : Nat) : ℝ) ≤ a * n := by
              have hnat := Finset.card_union_le IA IB
              have hreal :
                  (((IA ∪ IB).card : Nat) : ℝ) ≤ IA.card + IB.card := by
                exact_mod_cast hnat
              nlinarith
            have himply :=
              union_implies_resolvent f hIA hIB hres
            refine ⟨_, Or.inr rfl,
              complex_not_partialSatisfies f ha hcomplex, ?_⟩
            exact implied_clause_large_of_complex hbased hP f hDsmall
              hunionCard himply hcomplex
  apply hstep href.1
  exact ⟨∅, href.2, empty_complex_of_specialDomain f hspecial⟩

/-- The special-pair form of (6.3), deriving the domain-size estimate from
`s = ⌊bn⌋` and `b ≤ a/8`. -/
theorem specialPair_refutation_has_large_unsatisfied_clause
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F) (hP : H.HasPropertyP a)
    (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hba : b ≤ a / 8)
    (ha2 : 2 ≤ a * n)
    (p : SpecialPair F a ⌊b * n⌋₊ ha)
    {cs : List (Clause n)} (href : ResolutionRefutation F cs) :
    ∃ C ∈ cs, ¬ PartialSatisfiesClause p.2 C ∧
      a * n / 8 < (clauseVarSet C).card := by
  classical
  let D := exactSpecialDomain F a ⌊b * n⌋₊ p.1 ha
  have hDsub : D ⊆ p.1.val :=
    exactSpecialDomain_subset F a ⌊b * n⌋₊ p.1 ha
  have hScard : p.1.val.card = ⌊b * n⌋₊ := by
    have hp := p.1.property
    simpa [specialSets] using
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).2
  have hsbn : (⌊b * n⌋₊ : ℝ) ≤ b * n :=
    Nat.floor_le (mul_nonneg hb0 (Nat.cast_nonneg n))
  have hDsmall : (D.card : ℝ) ≤ a * n / 8 := by
    calc
      (D.card : ℝ) ≤ p.1.val.card := by
        exact_mod_cast Finset.card_le_card hDsub
      _ = (⌊b * n⌋₊ : Nat) := by rw [hScard]
      _ ≤ b * n := hsbn
      _ ≤ (a / 8) * n := by gcongr
      _ = a * n / 8 := by ring
  exact resolutionRefutation_has_large_unsatisfied_clause
    hbased hP ha ha2 p.2
      (exactSpecialDomain_special F a ⌊b * n⌋₊ p.1 ha)
      hDsmall href

end AvgCaseMls.Section3
