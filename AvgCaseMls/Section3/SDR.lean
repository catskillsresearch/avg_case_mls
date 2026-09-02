/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson, Catskills Research Company
-/

import AvgCaseMls.Section3.Hypergraph

/-!
# Chvátal--Szemerédi's constrained SDR lemma
-/

namespace AvgCaseMls.Section3

/-- CS87 Lemma 2, including both directions and the exact deficiency
condition (4.2). -/
theorem familyHasSDRWithAtMost_iff {ι α : Type*}
    [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α]
    (E : ι → Finset α) (S : Finset α) (t : Nat) :
    FamilyHasSDRWithAtMost E S t ↔
      FamilyHasSDR E ∧
        ∀ J : Finset ι,
          J.card - (J.biUnion fun i => E i \ S).card ≤ t := by
  constructor
  · exact familyHasSDRWithAtMost_onlyIf E S t
  · rintro ⟨hsdr, hdef⟩
    classical
    rcases hsdr with ⟨f₀, hf₀, hf₀mem⟩
    by_cases hSt : S.card ≤ t
    · refine ⟨f₀, hf₀, hf₀mem, ?_⟩
      calc
        (Finset.univ.filter fun i => f₀ i ∈ S).card
            = ((Finset.univ.filter fun i => f₀ i ∈ S).image f₀).card := by
              rw [Finset.card_image_of_injective _ hf₀]
        _ ≤ S.card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_image] at hx
          rcases hx with ⟨i, hi, rfl⟩
          exact (Finset.mem_filter.mp hi).2
        _ ≤ t := hSt
    · have htS : t < S.card := Nat.lt_of_not_ge hSt
      let q := S.card - t
      let T : (ι ⊕ Fin q) → Finset α :=
        Sum.elim E (fun _ => S)
      have hhallT : ∀ K : Finset (ι ⊕ Fin q),
          K.card ≤ (K.biUnion T).card := by
        intro K
        have hcardK :
            K.toLeft.card + K.toRight.card = K.card :=
          Finset.card_toLeft_add_card_toRight
        by_cases hR : K.toRight.Nonempty
        · let O := K.toLeft.biUnion fun i => E i \ S
          have hL : K.toLeft.card ≤ O.card + t := by
            have hd := hdef K.toLeft
            dsimp [O]
            omega
          have hRcard : K.toRight.card ≤ q := by
            calc
              K.toRight.card ≤ Fintype.card (Fin q) :=
                Finset.card_le_univ _
              _ = q := Fintype.card_fin q
          have hSOcard : (S ∪ O).card = S.card + O.card := by
            rw [Finset.card_union_of_disjoint]
            rw [Finset.disjoint_left]
            intro x hxS hxO
            simp only [O, Finset.mem_biUnion, Finset.mem_sdiff] at hxO
            rcases hxO with ⟨i, _, _, hxnot⟩
            exact hxnot hxS
          have hSOsub : S ∪ O ⊆ K.biUnion T := by
            intro x hx
            rcases Finset.mem_union.mp hx with hxS | hxO
            · rcases hR with ⟨r, hr⟩
              exact Finset.mem_biUnion.mpr
                ⟨Sum.inr r, (Finset.mem_toRight.mp hr), hxS⟩
            · simp only [O, Finset.mem_biUnion, Finset.mem_sdiff] at hxO
              rcases hxO with ⟨i, hi, hxi, _⟩
              exact Finset.mem_biUnion.mpr
                ⟨Sum.inl i, Finset.mem_toLeft.mp hi, hxi⟩
          have htq : t + q = S.card := by
            dsimp [q]
            omega
          calc
            K.card = K.toLeft.card + K.toRight.card := hcardK.symm
            _ ≤ (O.card + t) + q := Nat.add_le_add hL hRcard
            _ = S.card + O.card := by omega
            _ = (S ∪ O).card := hSOcard.symm
            _ ≤ (K.biUnion T).card := Finset.card_le_card hSOsub
        · have hRe : K.toRight = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hR
          have hhallE :
              K.toLeft.card ≤
                (K.toLeft.biUnion E).card := by
            exact
              (Finset.all_card_le_biUnion_card_iff_existsInjective' E).mpr
                ⟨f₀, hf₀, hf₀mem⟩ K.toLeft
          have hunion :
              K.biUnion T = K.toLeft.biUnion E := by
            ext x
            simp only [Finset.mem_biUnion]
            constructor
            · rintro ⟨z, hzK, hxT⟩
              rcases z with i | r
              · exact ⟨i, Finset.mem_toLeft.mpr hzK, hxT⟩
              · have : r ∈ K.toRight := Finset.mem_toRight.mpr hzK
                rw [hRe] at this
                simp at this
            · rintro ⟨i, hi, hxi⟩
              exact ⟨Sum.inl i, Finset.mem_toLeft.mp hi, hxi⟩
          rw [hunion]
          rw [← hcardK, hRe]
          simpa using hhallE
      rcases
          (Finset.all_card_le_biUnion_card_iff_existsInjective' T).mp hhallT with
        ⟨g, hg, hgmem⟩
      let f : ι → α := fun i => g (Sum.inl i)
      have hf : Function.Injective f := hg.comp Sum.inl_injective
      have hfmem : ∀ i, f i ∈ E i := fun i => hgmem (Sum.inl i)
      refine ⟨f, hf, hfmem, ?_⟩
      let A := Finset.univ.filter fun i => f i ∈ S
      let imageA := A.image f
      let imageR := Finset.univ.image fun r : Fin q => g (Sum.inr r)
      have hAcard : imageA.card = A.card := by
        exact Finset.card_image_of_injective A hf
      have hRcard : imageR.card = q := by
        rw [Finset.card_image_of_injective]
        · simp
        · exact hg.comp Sum.inr_injective
      have hdisj : Disjoint imageA imageR := by
        rw [Finset.disjoint_left]
        intro x hxA hxR
        simp only [imageA, imageR, Finset.mem_image] at hxA hxR
        rcases hxA with ⟨i, hiA, hix⟩
        rcases hxR with ⟨r, _, hrx⟩
        have := hg (hix.trans hrx.symm)
        exact Sum.inl_ne_inr this
      have hunionSub : imageA ∪ imageR ⊆ S := by
        intro x hx
        rcases Finset.mem_union.mp hx with hxA | hxR
        · simp only [imageA, Finset.mem_image] at hxA
          rcases hxA with ⟨i, hiA, rfl⟩
          exact (Finset.mem_filter.mp hiA).2
        · simp only [imageR, Finset.mem_image] at hxR
          rcases hxR with ⟨r, _, rfl⟩
          exact hgmem (Sum.inr r)
      have hsum : A.card + q ≤ S.card := by
        rw [← hAcard, ← hRcard, ← Finset.card_union_of_disjoint hdisj]
        exact Finset.card_le_card hunionSub
      change A.card ≤ t
      dsimp [q] at hsum
      omega

end AvgCaseMls.Section3
