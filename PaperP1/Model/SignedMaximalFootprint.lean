module

public import PaperP1.Model.SignedPrivateDyadicField

/-! # A type-independent maximal footprint for the actual specified forcing -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedMaximalFootprint

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.SignedPrivateField
  PaperP1.PrivatePivotGeometry PaperP1.PrivatePrimeForcing PaperP1.OddPrimePivot
  PaperP1.PrivateDirectedFootprint PaperP1.ReciprocalOddPivots

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem mem_directed_footprint {M : ℕ} {ι : Type*} [Fintype ι]
    (G : Finset ℕ) (Q : ℕ) (q : ι → PrimeUpTo M) (k : ℕ) :
    k ∈ directedFootprint G Q q ↔ k ∈ G ∧
      ∃ i : ι, ∃ t : Fin (Q + 1), (q i).val.val ∣ k + t.val := by
  unfold directedFootprint
  exact mem_filter

variable {M Y L E : ℕ} {J : Finset ℕ}

def maximalPivots (D : Data M Y L E J) (j : J) : Fin (L + E + 2) → PrimeUpTo M :=
  cylinderPivot (D.boundary_pos j.val j.property) (D.cutoff j.val j.property)
    (fun i ↦ (small_pos D).trans_lt (D.good j.val j.property i))

def siteFootprint (D : Data M Y L E J) (j : J) : Finset J :=
  univ.filter fun k ↦ ∃ i : Fin (L + E + 2), ∃ t : Fin (L + E + 2),
    (maximalPivots D j i).val.val ∣ k.val + t.val

theorem actual_subset (D : Data M Y L E J) (a b : Index J E) (hb : b ∈ footprint D a) :
    b.1 ∈ siteFootprint D a.1 := by
  obtain ⟨_, i, t, hdiv⟩ := mem_filter.mp hb
  refine mem_filter.mpr ⟨mem_univ _, ⟨Fin.castLE (by have := a.2.1.isLt; omega) i, t, ?_⟩⟩
  exact hdiv

theorem card_le_interval (D : Data M Y L E J) (U N : ℕ)
    (hJ : J ⊆ Ico U (U + N)) (j : J) :
    (siteFootprint D j).card ≤
      (directedFootprint (Ico U (U + N)) (L + E + 1) (maximalPivots D j)).card := by
  apply card_le_card_of_injOn (fun k : J ↦ k.val)
  · intro k hk
    obtain ⟨_, i, t, hdiv⟩ := mem_filter.mp hk
    exact (mem_directed_footprint _ _ _ _).mpr ⟨hJ k.property, ⟨i, t, hdiv⟩⟩
  · intro k _ l _ h
    exact Subtype.ext h

theorem total_card_bound (D : Data M Y L E J) (U N X : ℕ)
    (hJ : J ⊆ Ico U (U + N))
    (hX : ∀ j ∈ J, ∀ i : Fin (L + E + 2), j + i.val ∈ Icc 1 X) :
    (∑ j : J, ((siteFootprint D j).card : ℝ)) ≤
      (L + E + 2 : ℝ) * ((N : ℝ) * (L + E + 2) * pivotSum X + (J.card : ℝ) * (L + E + 2)) := by
  have hlocal (j : J) : ((siteFootprint D j).card : ℝ) ≤
      (L + E + 2 : ℝ) * ((N : ℝ) *
        (∑ i : Fin (L + E + 2), 1 / (largestOddPrime (j.val + i.val) : ℝ)) + (L + E + 2)) := by
    have hc : ((siteFootprint D j).card : ℝ) ≤
        (directedFootprint (Ico U (U + N)) (L + E + 1) (maximalPivots D j)).card := by
      exact_mod_cast card_le_interval D U N hJ j
    have hf := footprint_card_real U N (L + E + 1) (maximalPivots D j)
    norm_num only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] at hf
    exact hc.trans (by simpa only [maximalPivots, cylinderPivot, add_assoc] using hf)
  have hp : (∑ j : J, ∑ i : Fin (L + E + 2),
      1 / (largestOddPrime (j.val + i.val) : ℝ)) ≤ (L + E + 2 : ℝ) * pivotSum X := by
    rw [sum_coe_sort J (fun j : ℕ ↦ ∑ i : Fin (L + E + 2),
      1 / (largestOddPrime (j + i.val) : ℝ))]
    have hh := word_pivot_sum_le J X (L + E + 2) hX
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hh
  calc
    _ ≤ ∑ j : J, (L + E + 2 : ℝ) * ((N : ℝ) *
        (∑ i : Fin (L + E + 2), 1 / (largestOddPrime (j.val + i.val) : ℝ)) + (L + E + 2)) :=
      sum_le_sum (fun j _ ↦ hlocal j)
    _ = (L + E + 2 : ℝ) * ((N : ℝ) *
        (∑ j : J, ∑ i : Fin (L + E + 2), 1 / (largestOddPrime (j.val + i.val) : ℝ)) +
          (J.card : ℝ) * (L + E + 2)) := by
      simp only [← mul_sum, sum_add_distrib, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ N)
      have ht := mul_le_mul_of_nonneg_left
        (add_le_add_right hh ((J.card : ℝ) * (L + E + 2))) (by positivity : (0 : ℝ) ≤ L + E + 2)
      simpa only [mul_assoc, add_comm] using ht

end PaperP1.SignedMaximalFootprint
