import AvgCaseMls.Section3.Lemma4

/-!
# CS87 Lemma 5: partial assignments and clause families based on a hypergraph

This file formalizes the semantic part of §6: ordinary clause families based
on an indexed hypergraph, special sets and pairs, and the assignment obtained
from an SDR avoiding the domain of a partial assignment.
-/

namespace AvgCaseMls.Section3

/-- The variables occurring in a clause.  For an ordinary clause this is
CS87's `E(C)`. -/
def clauseVarSet (C : Clause n) : Finset (Fin n) :=
  C.image Literal.varOf

/-- `C` contains at most one literal over each variable. -/
def IsOrdinaryClause (C : Clause n) : Prop :=
  ∀ ⦃l₁⦄, l₁ ∈ C → ∀ ⦃l₂⦄, l₂ ∈ C →
    l₁.varOf = l₂.varOf → l₁ = l₂

/-- CS87's assertion that the indexed clause family is based on `H`. -/
def ClauseFamilyBasedOn (H : Hypergraph n m) (F : Fin m → Clause n) : Prop :=
  ∀ i, IsOrdinaryClause (F i) ∧ clauseVarSet (F i) = H.edge i

/-- A truth assignment whose domain is the finite set `D`. -/
abbrev PartialAssignment {n : Nat} (D : Finset (Fin n)) := D → Bool

def ExtendsPartial {D : Finset (Fin n)}
    (a : Assignment n) (f : PartialAssignment D) : Prop :=
  ∀ x : D, a x.val = f x

def SatisfiesIndexedFamily (a : Assignment n) (F : Fin m → Clause n)
    (I : Finset (Fin m)) : Prop :=
  ∀ i ∈ I, SatisfiesClause a (F i)

/-- `f` already satisfies `C` if a literal whose variable lies in its domain
is true.  Thus `¬ PartialSatisfiesClause f C` is the condition used in the
counting argument following (6.3). -/
def PartialSatisfiesClause {D : Finset (Fin n)}
    (f : PartialAssignment D) (C : Clause n) : Prop :=
  ∃ l ∈ C, ∃ h : l.varOf ∈ D,
    (if l.2 then f ⟨l.1, h⟩ else !(f ⟨l.1, h⟩)) = true

theorem satisfiesClause_of_partialSatisfies
    {D : Finset (Fin n)} (f : PartialAssignment D) (C : Clause n)
    {a : Assignment n} (ha : ExtendsPartial a f)
    (h : PartialSatisfiesClause f C) :
    SatisfiesClause a C := by
  rcases h with ⟨l, hl, hD, heval⟩
  refine ⟨l, hl, ?_⟩
  rcases l with ⟨x, sign⟩
  simp only [evalLiteral] at heval ⊢
  have hax : a x = f ⟨x, hD⟩ := ha ⟨x, hD⟩
  cases sign <;> simp_all

/-- A domain on which every partial assignment extends to satisfy every
small indexed subfamily. -/
def IsSpecialDomain (F : Fin m → Clause n) (a : ℝ)
    (D : Finset (Fin n)) : Prop :=
  ∀ f : PartialAssignment D, ∀ I : Finset (Fin m),
    (I.card : ℝ) ≤ a * n →
      ∃ g : Assignment n, ExtendsPartial g f ∧
        SatisfiesIndexedFamily g F I

/-- The source's special `s`-sets, retaining a witness domain of the prescribed
size up to the exact `a|S|/32` deletion bound supplied by property Q. -/
def IsSpecialSet (F : Fin m → Clause n) (a : ℝ) (s : Nat)
    (S : Finset (Fin n)) : Prop :=
  S.card = s ∧ ∃ D ⊆ S,
    ((S \ D).card : ℝ) ≤ (a / 32) * S.card ∧
      IsSpecialDomain F a D

noncomputable def specialSets (F : Fin m → Clause n) (a : ℝ) (s : Nat) :
    Finset (Finset (Fin n)) := by
  classical
  exact ((Finset.univ : Finset (Fin n)).powersetCard s).filter
    fun S => IsSpecialSet F a s S

theorem mem_clauseVarSet_iff (C : Clause n) (x : Fin n) :
    x ∈ clauseVarSet C ↔ ∃ l ∈ C, l.varOf = x := by
  simp [clauseVarSet]

theorem basedOn_literal_at_edge
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F) (i : Fin m) {x : Fin n}
    (hx : x ∈ H.edge i) :
    ∃ l ∈ F i, l.varOf = x := by
  rw [← (hbased i).2, mem_clauseVarSet_iff] at hx
  exact hx

/-- The assignment-injection construction in CS87 §6: distinct
representatives outside `D` can independently be given the signs that satisfy
their corresponding clauses. -/
theorem exists_extension_satisfying_of_sdr
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F)
    (I : Finset (Fin m)) (D : Finset (Fin n))
    (hsdr : H.HasSDRDisjointFrom I D)
    (f : PartialAssignment D) :
    ∃ g : Assignment n, ExtendsPartial g f ∧
      SatisfiesIndexedFamily g F I := by
  classical
  rcases hsdr with ⟨r, hrinj, hrmem, hrD⟩
  let lit : I → Literal n := fun i =>
    Classical.choose (basedOn_literal_at_edge hbased i.val (hrmem i))
  have hlit_mem : ∀ i : I, lit i ∈ F i := fun i =>
    (Classical.choose_spec
      (basedOn_literal_at_edge hbased i.val (hrmem i))).1
  have hlit_var : ∀ i : I, (lit i).varOf = r i := fun i =>
    (Classical.choose_spec
      (basedOn_literal_at_edge hbased i.val (hrmem i))).2
  let g : Assignment n := fun x =>
    if hx : x ∈ D then f ⟨x, hx⟩
    else if hi : ∃ i : I, r i = x then (lit (Classical.choose hi)).2
    else false
  refine ⟨g, ?_, ?_⟩
  · intro x
    simp [g, x.property]
  · intro i hi
    let ii : I := ⟨i, hi⟩
    refine ⟨lit ii, hlit_mem ii, ?_⟩
    have hnotD : r ii ∉ D := hrD ii
    have hex : ∃ j : I, r j = r ii := ⟨ii, rfl⟩
    have hchosen : Classical.choose hex = ii := by
      apply hrinj
      exact Classical.choose_spec hex
    have hgval : g (r ii) = (lit ii).2 := by
      simp only [g, hnotD, ↓reduceDIte]
      rw [dif_pos hex, hchosen]
    have hvar := hlit_var ii
    rcases hli : lit ii with ⟨x, sign⟩
    simp only [Literal.varOf] at hvar
    have hx : x = r ii := by
      calc
        x = (lit ii).1 := by
          simpa using (congrArg Prod.fst hli).symm
        _ = r ii := hvar
    subst x
    cases sign <;> simp [evalLiteral, hgval, hli]

theorem isSpecialDomain_of_sdr_disjoint
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F) (a : ℝ)
    (D : Finset (Fin n))
    (hD : ∀ I : Finset (Fin m), (I.card : ℝ) ≤ a * n →
      H.HasSDRDisjointFrom I D) :
    IsSpecialDomain F a D := by
  intro f I hI
  exact exists_extension_satisfying_of_sdr hbased I D (hD I hI) f

theorem isSpecialDomain_mono
    {F : Fin m → Clause n} {a : ℝ}
    {D D' : Finset (Fin n)} (hsub : D' ⊆ D)
    (hD : IsSpecialDomain F a D) :
    IsSpecialDomain F a D' := by
  classical
  intro f I hI
  let f' : PartialAssignment D := fun x =>
    if hx : x.val ∈ D' then f ⟨x.val, hx⟩ else false
  rcases hD f' I hI with ⟨g, hg, hsat⟩
  refine ⟨g, ?_, hsat⟩
  intro x
  have hxD : x.val ∈ D := hsub x.property
  have := hg ⟨x.val, hxD⟩
  simpa [f', x.property] using this

/-- Every `Q`-good set is a special set.  This is the exact bridge from
property `Q(a,b)` to the special-pair argument. -/
theorem isSpecialSet_of_isQGoodSet
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F) (a : ℝ) (s : Nat)
    {S : Finset (Fin n)} (hS : H.IsQGoodSet a s S) :
    IsSpecialSet F a s S := by
  rcases hS with ⟨hcard, D, hDS, hsmall, havoid⟩
  exact ⟨hcard, D, hDS, hsmall,
    isSpecialDomain_of_sdr_disjoint hbased a D havoid⟩

/-- The exact domain cardinality `d` chosen in (6.1). -/
noncomputable def specialDomainSize (a : ℝ) (s : Nat) : Nat :=
  s - ⌊(a / 32) * s⌋₊

/-- A source-special set admits a special domain of exactly the cardinality
used to count special pairs. -/
theorem exists_exact_specialDomain
    {F : Fin m → Clause n} {a : ℝ} {s : Nat}
    {S : Finset (Fin n)} (_ha : 0 ≤ a)
    (hS : IsSpecialSet F a s S) :
    ∃ D : Finset (Fin n), D ⊆ S ∧
      D.card = specialDomainSize a s ∧ IsSpecialDomain F a D := by
  rcases hS with ⟨hScard, D, hDS, hsmall, hspecial⟩
  have hfloor :
      (S \ D).card ≤ ⌊(a / 32) * s⌋₊ := by
    apply Nat.le_floor
    rw [← hScard]
    exact hsmall
  have hDcard : specialDomainSize a s ≤ D.card := by
    have hDle : D.card ≤ S.card := Finset.card_le_card hDS
    have heq : s - (S \ D).card = D.card := by
      rw [Finset.card_sdiff_of_subset hDS, hScard]
      exact Nat.sub_sub_self (by simpa [hScard] using hDle)
    unfold specialDomainSize
    calc
      s - ⌊a / 32 * (s : ℝ)⌋₊ ≤ s - (S \ D).card :=
        Nat.sub_le_sub_left hfloor s
      _ = D.card := heq
  rcases Finset.exists_subset_card_eq hDcard with ⟨D', hD'D, hcard⟩
  exact ⟨D', hD'D.trans hDS, hcard,
    isSpecialDomain_mono hD'D hspecial⟩

noncomputable def exactSpecialDomain
    (F : Fin m → Clause n) (a : ℝ) (s : Nat)
    (S : {S // S ∈ specialSets F a s}) (ha : 0 ≤ a) :
    Finset (Fin n) := by
  classical
  exact Classical.choose (exists_exact_specialDomain ha
    (by simpa [specialSets] using (Finset.mem_filter.mp S.property).2))

theorem exactSpecialDomain_subset
    (F : Fin m → Clause n) (a : ℝ) (s : Nat)
    (S : {S // S ∈ specialSets F a s}) (ha : 0 ≤ a) :
    exactSpecialDomain F a s S ha ⊆ S.val := by
  classical
  exact (Classical.choose_spec (exists_exact_specialDomain ha
    (by simpa [specialSets] using
      (Finset.mem_filter.mp S.property).2))).1

theorem exactSpecialDomain_card
    (F : Fin m → Clause n) (a : ℝ) (s : Nat)
    (S : {S // S ∈ specialSets F a s}) (ha : 0 ≤ a) :
    (exactSpecialDomain F a s S ha).card = specialDomainSize a s := by
  classical
  exact (Classical.choose_spec (exists_exact_specialDomain ha
    (by simpa [specialSets] using
      (Finset.mem_filter.mp S.property).2))).2.1

theorem exactSpecialDomain_sdiff_card
    (F : Fin m → Clause n) (a : ℝ) (s : Nat)
    (S : {S // S ∈ specialSets F a s}) (ha : 0 ≤ a)
    (hfloor : ⌊(a / 32) * s⌋₊ ≤ s) :
    (S.val \ exactSpecialDomain F a s S ha).card =
      ⌊(a / 32) * s⌋₊ := by
  classical
  have hScard : S.val.card = s := by
    have hmem := S.property
    simpa [specialSets] using
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hmem).1).2
  rw [Finset.card_sdiff_of_subset
    (exactSpecialDomain_subset F a s S ha),
    exactSpecialDomain_card, specialDomainSize, hScard]
  exact Nat.sub_sub_self hfloor

theorem exactSpecialDomain_special
    (F : Fin m → Clause n) (a : ℝ) (s : Nat)
    (S : {S // S ∈ specialSets F a s}) (ha : 0 ≤ a) :
    IsSpecialDomain F a (exactSpecialDomain F a s S ha) := by
  classical
  exact (Classical.choose_spec (exists_exact_specialDomain ha
    (by simpa [specialSets] using
      (Finset.mem_filter.mp S.property).2))).2.2

/-- CS87's special pairs `(S,f)`, with a canonical exact-size domain chosen
for every special set. -/
abbrev SpecialPair (F : Fin m → Clause n) (a : ℝ) (s : Nat)
    (ha : 0 ≤ a) :=
  Sigma fun S : {S // S ∈ specialSets F a s} =>
    PartialAssignment (exactSpecialDomain F a s S ha)

/-- Equation (6.1) before applying the property-Q half-density estimate:
each special set has exactly `2^d` special pairs. -/
theorem specialPair_card
    (F : Fin m → Clause n) (a : ℝ) (s : Nat) (ha : 0 ≤ a) :
    Fintype.card (SpecialPair F a s ha) =
      (specialSets F a s).card * 2 ^ specialDomainSize a s := by
  classical
  change Fintype.card
      (Sigma fun S : {S // S ∈ specialSets F a s} =>
        PartialAssignment (exactSpecialDomain F a s S ha)) =
    (specialSets F a s).card * 2 ^ specialDomainSize a s
  calc
    _ = ∑ S : {S // S ∈ specialSets F a s},
        Fintype.card
          (PartialAssignment (exactSpecialDomain F a s S ha)) :=
      Fintype.card_sigma
    _ = ∑ _S : {S // S ∈ specialSets F a s},
        2 ^ specialDomainSize a s := by
      apply Finset.sum_congr rfl
      intro S _
      simp [exactSpecialDomain_card]
    _ = (specialSets F a s).card * 2 ^ specialDomainSize a s := by
      simp

/-- At least half of all `s = ⌊bn⌋` sets are special. -/
theorem twice_specialSets_card_ge_of_propertyQ
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F) (a b : ℝ)
    (hQ : H.HasPropertyQ a b) :
    ((Finset.univ : Finset (Fin n)).powersetCard ⌊b * n⌋₊).card ≤
      2 * (specialSets F a ⌊b * n⌋₊).card := by
  classical
  let Ω := (Finset.univ : Finset (Fin n)).powersetCard ⌊b * n⌋₊
  have hsub :
      (Ω.filter fun S => H.IsQGoodSet a ⌊b * n⌋₊ S) ⊆
        specialSets F a ⌊b * n⌋₊ := by
    intro S hS
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hS).1,
        isSpecialSet_of_isQGoodSet hbased a _ (Finset.mem_filter.mp hS).2⟩
  change Ω.card ≤ 2 * (specialSets F a ⌊b * n⌋₊).card
  calc
    Ω.card ≤ 2 * (Ω.filter fun S =>
        H.IsQGoodSet a ⌊b * n⌋₊ S).card := by
      simpa [Hypergraph.HasPropertyQ, Ω] using hQ
    _ ≤ 2 * (specialSets F a ⌊b * n⌋₊).card :=
      Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)

/-- Equation (6.1), in division-free natural-number form. -/
theorem specialPair_lower_bound_of_propertyQ
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F) (a b : ℝ) (ha : 0 ≤ a)
    (hQ : H.HasPropertyQ a b) :
    ((Finset.univ : Finset (Fin n)).powersetCard ⌊b * n⌋₊).card *
        2 ^ specialDomainSize a ⌊b * n⌋₊ ≤
      2 * Fintype.card (SpecialPair F a ⌊b * n⌋₊ ha) := by
  rw [specialPair_card]
  have hsets :=
    twice_specialSets_card_ge_of_propertyQ hbased a b hQ
  simpa [Nat.mul_assoc] using
    Nat.mul_le_mul_right (2 ^ specialDomainSize a ⌊b * n⌋₊) hsets

end AvgCaseMls.Section3
