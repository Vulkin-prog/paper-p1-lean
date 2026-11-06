module

public import PaperP1.Arithmetic.IntegerSplitProductCharacterEstimate
public import PaperP1.Arithmetic.SplitBranchPrimeCertificate

/-! # Unconditional uniform actual point counts for all bounded split-radical systems

The prime cutoff precedes every branch support, prime and coefficient vector.
The actual nonzero integer certificate excludes all reduction collisions.
Every nonempty branch union uses the internally proved character cancellation.
No source point estimate or projected-surface estimate is a premise.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalUniformPointEstimate

open Finset Polynomial SplitRadicalFiniteFieldPointCount
open BranchShiftReductionCertificate SplitBranchPrimeCertificate
open scoped Classical

theorem relative_error {F ι : Type*} [Field F] [Fintype F] [Fintype ι]
    (hodd : ringChar F ≠ 2) (c : ι → F) (I J : ι → Finset ℤ)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hcancel : ∀ s ∈ (univ : Finset ι).powerset.erase ∅,
      |((∑ x : F, quadraticChar F (linearValue F (s.biUnion I) x)) : ℝ)| ≤ δ * Fintype.card F ∨
      |((∑ y : F, quadraticChar F (linearValue F (s.biUnion J) y)) : ℝ)| ≤ δ * Fintype.card F) :
    |((points c I J).card : ℝ) - (Fintype.card F : ℝ)^2| ≤
      ((2 ^ Fintype.card ι - 1 : ℕ) : ℝ) * δ * (Fintype.card F : ℝ)^2 := by
  have hc : ((univ : Finset ι).powerset.erase ∅).card = 2 ^ Fintype.card ι - 1 := by
    rw [card_erase_of_mem (empty_mem_powerset (s := univ)), card_powerset, card_univ]
  have hb := PaperP1.SeparatedQuadraticPointError.error_bound hodd c
    (fun i ↦ linearValue F (I i)) (fun i ↦ linearValue F (J i))
    (δ * Fintype.card F) (mul_nonneg hδ (Nat.cast_nonneg _)) (by
      intro s hs
      rw [character_sum_union I s (fun i _ j _ hij ↦ hI hij),
        character_sum_union J s (fun i _ j _ hij ↦ hJ hij)]
      simpa only [Int.cast_sum] using hcancel s hs)
  rw [hc] at hb
  change |((points c I J).card : ℝ) - (Fintype.card F : ℝ)^2| ≤ _ at hb
  convert hb using 1; ring

theorem uniform_absolute {ι : Type*} [Fintype ι] (D : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ I J : ι → Finset ℤ,
      (support I J).card ≤ D →
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
      ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
        ¬ (p : ℤ) ∣ certificate (support I J) →
        letI : Fact p.Prime := ⟨hp⟩
        ∀ c : ι → ZMod p,
          |((points c I J).card : ℝ) - (p : ℝ)^2| ≤ η * (p : ℝ)^2 := by
  let C : ℝ := ((2 ^ Fintype.card ι - 1 : ℕ) : ℝ)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  let δ : ℝ := η / (C+1)
  have hδ : 0 < δ := div_pos hη (by linarith only [hC])
  obtain ⟨K, hK⟩ := IntegerSplitProductCharacterEstimate.uniform_absolute D δ hδ
  refine ⟨K, ?_⟩
  intro I J hD hI hJ hne p hp hlarge hnot
  let : Fact p.Prime := ⟨hp⟩
  intro c
  have hdec : (fun a b : ZMod p ↦ Classical.propDecidable (a = b)) = ZMod.decidableEq p :=
    Subsingleton.elim _ _
  have hinj := injective_reduction (support I J) p hnot
  have hodd : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact prime_ne_two (support I J) p hnot
  have hcancel : ∀ s ∈ (univ : Finset ι).powerset.erase ∅,
      |((∑ x : ZMod p, quadraticChar (ZMod p) (linearValue (ZMod p) (s.biUnion I) x)) : ℝ)| ≤ δ * p ∨
      |((∑ y : ZMod p, quadraticChar (ZMod p) (linearValue (ZMod p) (s.biUnion J) y)) : ℝ)| ≤ δ * p := by
    intro s hs
    have hsne : s.Nonempty := nonempty_iff_ne_empty.mpr (mem_erase.mp hs).1
    rcases PaperP1.SmallSplitBranchPointBound.union_nonempty_or I J s hsne (fun i _ ↦ hne i) with hi | hj
    · left
      simpa only [Int.cast_sum] using (hK p hp hlarge (s.biUnion I) hi
        ((card_le_card (left_subset I J s)).trans hD)
        (fun a ha b hb he ↦ hinj (left_subset I J s ha) (left_subset I J s hb) he))
    · right
      simpa only [Int.cast_sum] using (hK p hp hlarge (s.biUnion J) hj
        ((card_le_card (right_subset I J s)).trans hD)
        (fun a ha b hb he ↦ hinj (right_subset I J s ha) (right_subset I J s hb) he))
  rw [← hdec] at hcancel
  have he := relative_error hodd c I J hI hJ δ (le_of_lt hδ)
    (by simpa only [ZMod.card] using hcancel)
  rw [ZMod.card] at he
  have hratio : C * δ ≤ η := by
    have heq : δ * (C+1) = η := div_mul_cancel₀ η (by linarith only [hC])
    nlinarith only [heq, le_of_lt hδ]
  exact he.trans (mul_le_mul_of_nonneg_right hratio (sq_nonneg (p : ℝ)))

theorem uniform_upper_bound {ι : Type*} [Fintype ι] (D : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ I J : ι → Finset ℤ,
      (support I J).card ≤ D →
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
      ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
        ¬ (p : ℤ) ∣ certificate (support I J) →
        letI : Fact p.Prime := ⟨hp⟩
        ∀ c : ι → ZMod p,
          ((points c I J).card : ℝ) ≤ (1+η) * (p : ℝ)^2 := by
  obtain ⟨K, hK⟩ := uniform_absolute (ι := ι) D η hη
  refine ⟨K, ?_⟩
  intro I J hD hI hJ hne p hp hlarge hnot
  let : Fact p.Prime := ⟨hp⟩
  intro c
  have he := hK I J hD hI hJ hne p hp hlarge hnot c
  have hl := le_abs_self (((points c I J).card : ℝ) - (p : ℝ)^2)
  nlinarith only [he, hl]

end PaperP1.SplitRadicalUniformPointEstimate
