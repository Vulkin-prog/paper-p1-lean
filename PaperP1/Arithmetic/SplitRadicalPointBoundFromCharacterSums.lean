module

public import PaperP1.Arithmetic.SplitRadicalFiniteFieldPointCount
public import PaperP1.Analysis.SquareRootPointErrorThreshold

/-! # Uniform actual source point bounds from explicit one-variable cancellation premises

The cancellation estimate is an explicit hypothesis. No general character-sum
bound, projection reduction or original T1.7 conclusion is asserted by this file.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalPointBoundFromCharacterSums

open Finset SplitRadicalFiniteFieldPointCount
open scoped Classical

theorem square_root_error {F ι : Type*} [Field F] [Fintype F] [Fintype ι]
    (hodd : ringChar F ≠ 2) (c : ι → F) (I J : ι → Finset ℤ)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) (C : ℝ) (hC : 0 ≤ C)
    (hcancel : ∀ s ∈ (univ : Finset ι).powerset.erase ∅,
      |((∑ x : F, quadraticChar F (linearValue F (s.biUnion I) x)) : ℝ)| ≤
          C * Real.sqrt (Fintype.card F) ∨
      |((∑ y : F, quadraticChar F (linearValue F (s.biUnion J) y)) : ℝ)| ≤
          C * Real.sqrt (Fintype.card F)) :
    |((points c I J).card : ℝ) - (Fintype.card F : ℝ) ^ 2| ≤
      ((2 ^ Fintype.card ι - 1 : ℕ) : ℝ) * C * (Fintype.card F : ℝ) *
        Real.sqrt (Fintype.card F) := by
  have hc : ((univ : Finset ι).powerset.erase ∅).card = 2 ^ Fintype.card ι - 1 := by
    rw [card_erase_of_mem (empty_mem_powerset (s := univ)), card_powerset, card_univ]
  have hb := SeparatedQuadraticPointError.error_bound hodd c
    (fun i ↦ linearValue F (I i)) (fun i ↦ linearValue F (J i))
    (C * Real.sqrt (Fintype.card F)) (mul_nonneg hC (Real.sqrt_nonneg _)) (by
      intro s hs
      rw [character_sum_union I s (fun i _ j _ hij ↦ hI hij),
        character_sum_union J s (fun i _ j _ hij ↦ hJ hij)]
      simpa only [Int.cast_sum] using hcancel s hs)
  rw [hc] at hb
  change |((points c I J).card : ℝ) - (Fintype.card F : ℝ) ^ 2| ≤ _ at hb
  convert hb using 1
  ring

theorem uniform_upper_bound {ι : Type*} [Fintype ι] (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (F : Type) [Field F] [Fintype F], K ≤ Fintype.card F → ringChar F ≠ 2 →
      ∀ (c : ι → F) (I J : ι → Finset ℤ),
        (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
        (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
        (∀ s ∈ (univ : Finset ι).powerset.erase ∅,
          |((∑ x : F, quadraticChar F (linearValue F (s.biUnion I) x)) : ℝ)| ≤
              C * Real.sqrt (Fintype.card F) ∨
          |((∑ y : F, quadraticChar F (linearValue F (s.biUnion J) y)) : ℝ)| ≤
              C * Real.sqrt (Fintype.card F)) →
        ((points c I J).card : ℝ) ≤ (1 + η) * (Fintype.card F : ℝ) ^ 2 := by
  let M : ℝ := ((2 ^ Fintype.card ι - 1 : ℕ) : ℝ) * C
  obtain ⟨K, hK⟩ := SquareRootPointErrorThreshold.exists_threshold M 0 η
    (mul_nonneg (Nat.cast_nonneg _) hC) (by positivity) hη
  refine ⟨K, ?_⟩
  intro F _ _ hlarge hodd c I J hI hJ hcancel
  have he := square_root_error hodd c I J hI hJ C hC hcancel
  have ht := hK (Fintype.card F) hlarge
  have hl := le_abs_self (((points c I J).card : ℝ) - (Fintype.card F : ℝ) ^ 2)
  dsimp only [M] at ht
  nlinarith only [he, ht, hl]

end PaperP1.SplitRadicalPointBoundFromCharacterSums
