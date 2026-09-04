import AvgCaseMls.Section3.Lemma5Hypergeometric
import AvgCaseMls.Section3.Lemma5Resolution

/-!
# CS87 Lemma 5: special-pair aggregation

This file completes the double count in §6.  Every special pair is assigned
one large clause of a refutation, the fibers of this assignment are bounded
by (6.4) and (6.5), and the common factors are cancelled.
-/

namespace AvgCaseMls.Section3

open scoped BigOperators

noncomputable def specialPairClause
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F) (hP : H.HasPropertyP a)
    (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hba : b ≤ a / 8)
    (ha2 : 2 ≤ a * n)
    {cs : List (Clause n)} (href : ResolutionRefutation F cs)
    (p : SpecialPair F a ⌊b * n⌋₊ ha) : Clause n :=
  Classical.choose
    (specialPair_refutation_has_large_unsatisfied_clause
      hbased hP ha hb0 hba ha2 p href)

theorem specialPairClause_spec
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F) (hP : H.HasPropertyP a)
    (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hba : b ≤ a / 8)
    (ha2 : 2 ≤ a * n)
    {cs : List (Clause n)} (href : ResolutionRefutation F cs)
    (p : SpecialPair F a ⌊b * n⌋₊ ha) :
    specialPairClause hbased hP ha hb0 hba ha2 href p ∈ cs ∧
      ¬ PartialSatisfiesClause p.2
        (specialPairClause hbased hP ha hb0 hba ha2 href p) ∧
      a * n / 8 <
        (clauseVarSet
          (specialPairClause hbased hP ha hb0 hba ha2 href p)).card :=
  Classical.choose_spec
    (specialPair_refutation_has_large_unsatisfied_clause
      hbased hP ha hb0 hba ha2 p href)

private theorem exactSpecialDomain_delete_card_le
    (F : Fin m → Clause n) (a : ℝ) (s : Nat)
    (S : {S // S ∈ specialSets F a s}) (ha : 0 ≤ a) :
    (S.val \ exactSpecialDomain F a s S ha).card ≤
      ⌊(a / 32) * s⌋₊ := by
  classical
  have hScard : S.val.card = s := by
    simpa [specialSets] using
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp S.property).1).2
  rw [Finset.card_sdiff_of_subset
    (exactSpecialDomain_subset F a s S ha),
    exactSpecialDomain_card, specialDomainSize, hScard]
  omega

private theorem low_domain_inter_implies_low_set_inter
    (F : Fin m → Clause n) (a : ℝ) (s : Nat)
    (S : {S // S ∈ specialSets F a s}) (ha : 0 ≤ a)
    (E : Finset (Fin n))
    (hsmall :
      ((exactSpecialDomain F a s S ha ∩ E).card : ℝ) ≤
        a * s / 32) :
    ((S.val ∩ E).card : ℝ) ≤ a * s / 16 := by
  classical
  let q := ⌊(a / 32) * s⌋₊
  have haq : 0 ≤ (a / 32) * (s : ℝ) := mul_nonneg (by positivity) (by positivity)
  have hDq :
      (exactSpecialDomain F a s S ha ∩ E).card ≤ q := by
    apply Nat.le_floor
    simpa [q, div_mul_eq_mul_div] using hsmall
  have hdel :
      (S.val \ exactSpecialDomain F a s S ha).card ≤ q :=
    exactSpecialDomain_delete_card_le F a s S ha
  have hnat :=
    card_inter_le_of_domain_inter_le
      (exactSpecialDomain_subset F a s S ha) hdel hDq
  have hq :
      (q : ℝ) ≤ (a / 32) * s := Nat.floor_le haq
  have hcast : ((S.val ∩ E).card : ℝ) ≤ q + q := by
    exact_mod_cast hnat
  nlinarith

private theorem pow_sub_le_rpow_of_large_inter
    {d i : Nat} {q : ℝ} (hid : i ≤ d) (hi : q < i) :
    ((2 ^ (d - i) : Nat) : ℝ) ≤
      (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ q := by
  have hsub :
      ((2 ^ (d - i) : Nat) : ℝ) ≤ (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ i := by
    push_cast
    rw [one_div, inv_pow, ← div_eq_mul_inv,
      pow_sub₀ (2 : ℝ) (by norm_num) hid]
    rw [div_eq_mul_inv]
  have hrpow :
      (1 / 2 : ℝ) ^ (i : ℝ) ≤ (1 / 2 : ℝ) ^ q :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (le_of_lt hi)
  rw [Real.rpow_natCast] at hrpow
  exact hsub.trans (mul_le_mul_of_nonneg_left hrpow (by positivity))

private theorem special_bad_count_le
    {F : Fin m → Clause n} (a : ℝ) (s : Nat) (ha : 0 ≤ a)
    (C : Clause n) (hn : 0 < n)
    (hlarge : a * n / 8 < (clauseVarSet C).card) :
    (∑ S : {S // S ∈ specialSets F a s},
        (badPartialAssignments
          (exactSpecialDomain F a s S ha) C).card : ℝ) ≤
      (n.choose s : ℝ) * (2 : ℝ) ^ specialDomainSize a s *
        ((2 / Real.exp 1) ^ (a * s / 16) +
          (1 / 2 : ℝ) ^ (a * s / 32)) := by
  classical
  let E := clauseVarSet C
  let d := specialDomainSize a s
  let q : ℝ := a * s / 32
  let r : ℝ := a * s / 16
  let lowSets :=
    (Finset.univ : Finset {S // S ∈ specialSets F a s}).filter fun S =>
      (((exactSpecialDomain F a s
        S ha ∩ E).card : Nat) : ℝ) ≤ q
  let highSets :=
    (Finset.univ : Finset {S // S ∈ specialSets F a s}).filter fun S =>
      q < (((exactSpecialDomain F a s
        S ha ∩ E).card : Nat) : ℝ)
  have hpartition :
      (∑ S : {S // S ∈ specialSets F a s},
          ((badPartialAssignments
            (exactSpecialDomain F a s S ha) C).card : ℝ)) =
        (∑ S ∈ lowSets,
          ((badPartialAssignments
            (exactSpecialDomain F a s S ha) C).card : ℝ)) +
        ∑ S ∈ highSets,
          ((badPartialAssignments
            (exactSpecialDomain F a s S ha) C).card : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset {S // S ∈ specialSets F a s}))
      (p := fun S =>
        (((exactSpecialDomain F a s S ha ∩ E).card : Nat) : ℝ) ≤ q)]
    simp only [lowSets, highSets, not_le]
  rw [hpartition]
  have hmn : E.card ≤ n := by
    simpa [E] using Finset.card_le_card
      (Finset.subset_univ E)
  have hmean : 2 * (n : ℝ) * r ≤ (E.card : ℝ) * s := by
    dsimp [r, E]
    have hs0 : (0 : ℝ) ≤ s := by positivity
    nlinarith
  have hhyp :=
    hypergeomLowerCountReal_le_cs87
      (n := n) (m := E.card) (s := s) (r := r) hn hmn hmean
  have hlowSets :
      lowSets.card ≤ hypergeomLowerCountReal n E.card s r := by
    rw [← card_powersetCard_filter_inter_le E s r]
    let vals := lowSets.image fun S => S.val
    have hcardvals : vals.card = lowSets.card := by
      rw [Finset.card_image_iff.mpr]
      intro S hS T hT h
      exact Subtype.ext h
    rw [← hcardvals]
    apply Finset.card_le_card
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
    have hT' := Finset.mem_filter.mp hT
    apply Finset.mem_filter.mpr
    exact ⟨(Finset.mem_filter.mp T.property).1,
      low_domain_inter_implies_low_set_inter F a s T ha E hT'.2⟩
  have hlow :
      (∑ S ∈ lowSets,
          ((badPartialAssignments
            (exactSpecialDomain F a s S ha) C).card : ℝ)) ≤
        (n.choose s : ℝ) * (2 : ℝ) ^ d *
          (2 / Real.exp 1) ^ r := by
    calc
      _ ≤ ∑ _S ∈ lowSets, (2 : ℝ) ^ d := by
        apply Finset.sum_le_sum
        intro S hS
        exact_mod_cast
          (show (badPartialAssignments
              (exactSpecialDomain F a s ⟨S.val, S.property⟩ ha) C).card ≤
              2 ^ d by
            calc
              _ ≤ 2 ^ ((exactSpecialDomain F a s
                  ⟨S.val, S.property⟩ ha).card -
                    ((exactSpecialDomain F a s
                      ⟨S.val, S.property⟩ ha) ∩ E).card) :=
                badPartialAssignments_card_le _ C
              _ ≤ 2 ^ d := by
                apply Nat.pow_le_pow_right (by omega)
                rw [exactSpecialDomain_card]
                omega)
      _ = (lowSets.card : ℝ) * (2 : ℝ) ^ d := by simp
      _ ≤ (hypergeomLowerCountReal n E.card s r : ℝ) *
          (2 : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hlowSets) (by positivity)
      _ ≤ ((n.choose s : ℝ) * (2 / Real.exp 1) ^ r) *
          (2 : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right hhyp (by positivity)
      _ = (n.choose s : ℝ) * (2 : ℝ) ^ d *
          (2 / Real.exp 1) ^ r := by ring
  have hhigh :
      (∑ S ∈ highSets,
          ((badPartialAssignments
            (exactSpecialDomain F a s S ha) C).card : ℝ)) ≤
        (n.choose s : ℝ) * (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ q := by
    calc
      _ ≤ ∑ _S ∈ highSets,
          (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ q := by
        apply Finset.sum_le_sum
        intro S hS
        have hi := (Finset.mem_filter.mp hS).2
        calc
          ((badPartialAssignments
              (exactSpecialDomain F a s S ha) C).card : ℝ) ≤
              ((2 ^ ((exactSpecialDomain F a s
                S ha).card -
                  ((exactSpecialDomain F a s
                    S ha) ∩ E).card) : Nat) : ℝ) := by
                exact_mod_cast badPartialAssignments_card_le
                  (exactSpecialDomain F a s
                    S ha) C
          _ ≤ (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ q := by
            rw [exactSpecialDomain_card]
            exact pow_sub_le_rpow_of_large_inter
              (by
                rw [← exactSpecialDomain_card F a s S ha]
                exact Finset.card_le_card Finset.inter_subset_left) hi
      _ = (highSets.card : ℝ) *
          ((2 : ℝ) ^ d * (1 / 2 : ℝ) ^ q) := by simp
      _ ≤ (n.choose s : ℝ) *
          ((2 : ℝ) ^ d * (1 / 2 : ℝ) ^ q) := by
        gcongr
        exact_mod_cast
          (calc
            highSets.card ≤ (specialSets F a s).card := by
              dsimp [highSets]
              calc
                ((Finset.univ :
                    Finset {S // S ∈ specialSets F a s}).filter fun S =>
                      q < ((exactSpecialDomain F a s S ha ∩ E).card : ℝ)).card ≤
                    (Finset.univ :
                      Finset {S // S ∈ specialSets F a s}).card :=
                  Finset.card_le_card (Finset.filter_subset _ _)
                _ = (specialSets F a s).card := by simp
            _ ≤ ((Finset.univ : Finset (Fin n)).powersetCard s).card := by
              exact Finset.card_le_card (Finset.filter_subset _ _)
            _ = n.choose s := by simp)
      _ = (n.choose s : ℝ) * (2 : ℝ) ^ d *
          (1 / 2 : ℝ) ^ q := by ring
  nlinarith

private theorem exp_one_sq_lt_eight :
    Real.exp 1 ^ 2 < (8 : ℝ) := by
  have hu := Real.exp_one_lt_d9
  have hp : 0 <
      (2.7182818286 : ℝ) - Real.exp 1 := sub_pos.mpr hu
  have hs : 0 <
      (2.7182818286 : ℝ) + Real.exp 1 := by positivity
  have hm := mul_pos hp hs
  have he : Real.exp 1 ^ 2 < (2.7182818286 : ℝ) ^ 2 := by
    nlinarith
  have hc : (2.7182818286 : ℝ) ^ 2 < 8 := by norm_num
  exact he.trans hc

/-- CS87 Lemma 5: properties P and Q force the exact exponential lower bound
on the minimum length of a resolution refutation. -/
theorem cs87_lemma5_of_two_le
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F)
    (hP : H.HasPropertyP a) (hQ : H.HasPropertyQ a b)
    (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hba : b ≤ a / 8)
    (ha2 : 2 ≤ a * n)
    (hrefutes : ∃ cs, ResolutionRefutation F cs) :
    (1 / 4 : ℝ) *
        (Real.exp 1 / 2) ^ (a * ⌊b * n⌋₊ / 16) ≤
      resolutionComplexity F := by
  classical
  let s := ⌊b * n⌋₊
  let d := specialDomainSize a s
  rcases resolutionComplexity_spec hrefutes with ⟨cs, href, hlen⟩
  let assign : SpecialPair F a s ha → {C // C ∈ cs} := fun p =>
    ⟨specialPairClause hbased hP ha hb0 hba ha2 href p,
      (specialPairClause_spec hbased hP ha hb0 hba ha2 href p).1⟩
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num at ha2
  have hfiber : ∀ C : {C // C ∈ cs},
      (Fintype.card {p : SpecialPair F a s ha // assign p = C} : ℝ) ≤
        (n.choose s : ℝ) * (2 : ℝ) ^ d *
          ((2 / Real.exp 1) ^ (a * s / 16) +
            (1 / 2 : ℝ) ^ (a * s / 32)) := by
    intro C
    by_cases hex : ∃ p : SpecialPair F a s ha, assign p = C
    · let intoBad :
          {p : SpecialPair F a s ha // assign p = C} →
            Sigma fun S : {S // S ∈ specialSets F a s} =>
              {f // f ∈ badPartialAssignments
                (exactSpecialDomain F a s S ha) C.val} := fun p =>
        ⟨p.val.1, p.val.2, by
          simp only [badPartialAssignments, Finset.mem_filter,
            Finset.mem_univ, true_and]
          have hu :=
            (specialPairClause_spec hbased hP ha hb0 hba ha2 href p.val).2.1
          have hc :
              specialPairClause hbased hP ha hb0 hba ha2 href p.val = C.val :=
            congrArg Subtype.val p.property
          simpa only [hc] using hu⟩
      have hinj : Function.Injective intoBad := by
        intro p q hpq
        apply Subtype.ext
        exact congrArg
          (fun z => (⟨z.1, z.2.val⟩ : SpecialPair F a s ha)) hpq
      have hcard := Fintype.card_le_of_injective intoBad hinj
      have hsum :
          Fintype.card
            (Sigma fun S : {S // S ∈ specialSets F a s} =>
              {f // f ∈ badPartialAssignments
                (exactSpecialDomain F a s S ha) C.val}) =
            ∑ S : {S // S ∈ specialSets F a s},
              (badPartialAssignments
                (exactSpecialDomain F a s S ha) C.val).card := by
        rw [Fintype.card_sigma]
        apply Finset.sum_congr rfl
        intro S hS
        exact Fintype.card_coe _
      rw [hsum] at hcard
      calc
        (Fintype.card {p : SpecialPair F a s ha // assign p = C} : ℝ) ≤
            ∑ S : {S // S ∈ specialSets F a s},
              ((badPartialAssignments
                (exactSpecialDomain F a s S ha) C.val).card : ℝ) := by
                  exact_mod_cast hcard
        _ ≤ _ := by
          simpa [d] using
            special_bad_count_le (F := F) a s ha C.val hn
              (by
                rcases hex with ⟨p, rfl⟩
                exact (specialPairClause_spec
                  hbased hP ha hb0 hba ha2 href p).2.2)
    · have hz :
          Fintype.card {p : SpecialPair F a s ha // assign p = C} = 0 := by
        apply Fintype.card_eq_zero_iff.mpr
        exact ⟨fun h => hex ⟨h, h.property⟩⟩
      rw [hz]
      norm_num
      positivity
  have htotal :
      (Fintype.card (SpecialPair F a s ha) : ℝ) ≤
        cs.length *
          ((n.choose s : ℝ) * (2 : ℝ) ^ d *
            ((2 / Real.exp 1) ^ (a * s / 16) +
              (1 / 2 : ℝ) ^ (a * s / 32))) := by
    have hsumfib :
        Fintype.card (SpecialPair F a s ha) =
          ∑ C : {C // C ∈ cs},
            Fintype.card {p : SpecialPair F a s ha // assign p = C} := by
      symm
      calc
        _ = Fintype.card
            (Sigma fun C : {C // C ∈ cs} =>
              {p : SpecialPair F a s ha // assign p = C}) := by
          rw [Fintype.card_sigma]
        _ = _ := Fintype.card_congr (Equiv.sigmaFiberEquiv assign)
    rw [hsumfib, Nat.cast_sum]
    calc
      _ ≤ ∑ _C : {C // C ∈ cs},
          ((n.choose s : ℝ) * (2 : ℝ) ^ d *
            ((2 / Real.exp 1) ^ (a * s / 16) +
              (1 / 2 : ℝ) ^ (a * s / 32))) :=
        Finset.sum_le_sum fun C _ => hfiber C
      _ = (Fintype.card {C // C ∈ cs} : ℝ) *
          ((n.choose s : ℝ) * (2 : ℝ) ^ d *
            ((2 / Real.exp 1) ^ (a * s / 16) +
              (1 / 2 : ℝ) ^ (a * s / 32))) := by simp
      _ ≤ _ := by
        gcongr
        exact_mod_cast
          (show Fintype.card {C // C ∈ cs} ≤ cs.length by
            let e : {C // C ∈ cs} ≃ {C // C ∈ cs.toFinset} :=
              Equiv.subtypeEquiv (Equiv.refl _) (fun C => by simp)
            rw [Fintype.card_congr e, Fintype.card_coe]
            exact List.toFinset_card_le cs)
  have hlower :=
    specialPair_lower_bound_of_propertyQ hbased a b ha hQ
  have hchoose : ((Finset.univ : Finset (Fin n)).powersetCard s).card =
      n.choose s := by simp [s]
  rw [hchoose, show ⌊b * n⌋₊ = s by rfl] at hlower
  have hpositive : 0 < (n.choose s : ℝ) * (2 : ℝ) ^ d := by
    have hsn : s ≤ n := by
      dsimp [s]
      exact Nat.floor_le_of_le (by
        calc
          b * (n : ℝ) ≤ 1 * n := by gcongr
          _ = n := one_mul _)
    have hchoosepos : 0 < n.choose s := Nat.choose_pos hsn
    positivity
  have hcombined :
      (n.choose s : ℝ) * (2 : ℝ) ^ d ≤
        2 * cs.length *
          ((n.choose s : ℝ) * (2 : ℝ) ^ d *
            ((2 / Real.exp 1) ^ (a * s / 16) +
              (1 / 2 : ℝ) ^ (a * s / 32))) := by
    have hlowerR :
        (n.choose s : ℝ) * (2 : ℝ) ^ d ≤
          2 * Fintype.card (SpecialPair F a s ha) := by
      exact_mod_cast hlower
    calc
      _ ≤ (2 : ℝ) * Fintype.card (SpecialPair F a s ha) := hlowerR
      _ ≤ (2 : ℝ) * (cs.length *
          ((n.choose s : ℝ) * (2 : ℝ) ^ d *
            ((2 / Real.exp 1) ^ (a * s / 16) +
              (1 / 2 : ℝ) ^ (a * s / 32)))) := by gcongr
      _ = _ := by ring
  let x : ℝ := a * s / 32
  let t : ℝ := (2 / Real.exp 1) ^ (a * s / 16)
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hbase : (1 / 2 : ℝ) ≤ (2 / Real.exp 1) ^ (2 : Nat) := by
    rw [div_pow]
    rw [le_div_iff₀ (by positivity : 0 < Real.exp 1 ^ (2 : Nat))]
    nlinarith [exp_one_sq_lt_eight]
  have htail : (1 / 2 : ℝ) ^ (a * s / 32) ≤ t := by
    have hp := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2)
      hbase hx
    dsimp [x] at hp
    rw [← Real.rpow_two] at hp
    have hrewrite :
        ((2 / Real.exp 1) ^ (2 : ℝ)) ^ (a * s / 32) =
          (2 / Real.exp 1) ^ (a * s / 16) := by
      rw [← Real.rpow_mul (by positivity : 0 ≤ 2 / Real.exp 1)]
      congr 1
      ring
    rw [hrewrite] at hp
    exact hp
  have hsum :
      (2 / Real.exp 1) ^ (a * s / 16) +
          (1 / 2 : ℝ) ^ (a * s / 32) ≤ 2 * t := by
    dsimp [t]
    linarith
  have hone :
      1 ≤ 2 * (cs.length : ℝ) *
        ((2 / Real.exp 1) ^ (a * s / 16) +
          (1 / 2 : ℝ) ^ (a * s / 32)) := by
    have hscaled :
        ((n.choose s : ℝ) * (2 : ℝ) ^ d) * 1 ≤
          ((n.choose s : ℝ) * (2 : ℝ) ^ d) *
            (2 * (cs.length : ℝ) *
              ((2 / Real.exp 1) ^ (a * s / 16) +
                (1 / 2 : ℝ) ^ (a * s / 32))) := by
      calc
        _ = (n.choose s : ℝ) * (2 : ℝ) ^ d := by ring
        _ ≤ _ := hcombined
        _ = _ := by ring
    nlinarith
  have hone' : 1 ≤ 4 * (cs.length : ℝ) * t := by
    calc
      1 ≤ 2 * (cs.length : ℝ) *
          ((2 / Real.exp 1) ^ (a * s / 16) +
            (1 / 2 : ℝ) ^ (a * s / 32)) := hone
      _ ≤ 2 * (cs.length : ℝ) * (2 * t) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 4 * (cs.length : ℝ) * t := by ring
  have hquarter : (1 / 4 : ℝ) ≤ (cs.length : ℝ) * t := by
    nlinarith
  have htpos : 0 < t := by
    dsimp [t]
    positivity
  have hinv :
      (Real.exp 1 / 2) ^ (a * s / 16) * t = 1 := by
    dsimp [t]
    rw [← Real.mul_rpow (by positivity : 0 ≤ Real.exp 1 / 2)
      (by positivity : 0 ≤ 2 / Real.exp 1)]
    have hmul : (Real.exp 1 / 2) * (2 / Real.exp 1) = 1 := by
      field_simp [Real.exp_ne_zero]
    rw [hmul, Real.one_rpow]
  rw [← hlen]
  have hmul :
      ((1 / 4 : ℝ) * (Real.exp 1 / 2) ^ (a * s / 16)) * t ≤
        (cs.length : ℝ) * t := by
    rw [mul_assoc, hinv, mul_one]
    exact hquarter
  have hfinal :
      (1 / 4 : ℝ) * (Real.exp 1 / 2) ^ (a * s / 16) ≤
        (cs.length : ℝ) := by
    nlinarith
  simpa [s] using hfinal

/-- CS87 Lemma 5, with the small `a n` case discharged directly. -/
theorem cs87_lemma5
    {H : Hypergraph n m} {F : Fin m → Clause n}
    (hbased : ClauseFamilyBasedOn H F)
    (hP : H.HasPropertyP a) (hQ : H.HasPropertyQ a b)
    (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hba : b ≤ a / 8)
    (hrefutes : ∃ cs, ResolutionRefutation F cs) :
    (1 / 4 : ℝ) *
        (Real.exp 1 / 2) ^ (a * ⌊b * n⌋₊ / 16) ≤
      resolutionComplexity F := by
  by_cases ha2 : 2 ≤ a * n
  · exact cs87_lemma5_of_two_le hbased hP hQ ha hb0 hb1 hba ha2 hrefutes
  · have han : a * (n : ℝ) < 2 := lt_of_not_ge ha2
    let s := ⌊b * n⌋₊
    have hsn : s ≤ n := by
      dsimp [s]
      exact Nat.floor_le_of_le (by
        calc
          b * (n : ℝ) ≤ 1 * n := by gcongr
          _ = n := one_mul _)
    have has : a * (s : ℝ) ≤ a * n := by
      gcongr
    have hr0 : 0 ≤ a * (s : ℝ) / 16 := by positivity
    have hr1 : a * (s : ℝ) / 16 ≤ 1 := by nlinarith
    have hbase0 : 0 ≤ Real.exp 1 / 2 := by positivity
    have hbase : Real.exp 1 / 2 ≤ (2 : ℝ) := by
      nlinarith [Real.exp_one_lt_three]
    have hpbase :
        (Real.exp 1 / 2) ^ (a * (s : ℝ) / 16) ≤
          (2 : ℝ) ^ (a * (s : ℝ) / 16) :=
      Real.rpow_le_rpow hbase0 hbase hr0
    have hpexp :
        (2 : ℝ) ^ (a * (s : ℝ) / 16) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hr1
    have hcomplexity : (1 : ℝ) ≤ resolutionComplexity F := by
      rcases resolutionComplexity_spec hrefutes with ⟨cs, href, hlen⟩
      rw [← hlen]
      exact_mod_cast (Nat.succ_le_iff.mpr (List.length_pos_of_mem href.2))
    calc
      (1 / 4 : ℝ) *
          (Real.exp 1 / 2) ^ (a * ⌊b * n⌋₊ / 16) =
          (1 / 4 : ℝ) *
            (Real.exp 1 / 2) ^ (a * (s : ℝ) / 16) := by rfl
      _ ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (1 : ℝ) := by
        gcongr
        exact hpbase.trans hpexp
      _ ≤ 1 := by norm_num [Real.rpow_one]
      _ ≤ resolutionComplexity F := hcomplexity

end AvgCaseMls.Section3
