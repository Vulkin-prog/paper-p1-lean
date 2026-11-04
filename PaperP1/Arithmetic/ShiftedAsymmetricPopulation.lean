module

public import PaperP1.Arithmetic.ShiftedAlignmentRadius
public import PaperP1.Model.FiniteRademacher

/-! # A dyadic population with large asymmetric loss outside radius-one alignment

The old set is the same deterministic interval-valued rule for every source.
Both centres lie in the single dyadic block [6m,12m). No root-counting or
geometric estimate is assumed in this construction.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShiftedAsymmetricPopulation

open Finset PaperP1.Model PaperP1.AsymmetricShiftedWitness PaperP1.AsymmetricEvenLoss

def centres (m k : ℕ) : Finset ℕ := Ico (3 * m) (4 * m - width k)

def pairs (m k : ℕ) : Finset (ℕ × ℕ) :=
  (centres m k).image (fun t ↦ (source t, target t k))

def weight (H k : ℕ) (p : ℕ × ℕ) : ℝ :=
  (2 : ℝ) ^ loss H (oldValues p.1 k) p.2 (3 * k) - 1

def population (N k : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter
    (fun p ↦ ¬CompressedTargetAlignment.Aligned 1 p.1 p.2 (3 * k))

def total (N H k : ℕ) : ℝ := ∑ p ∈ population N k, weight H k p

theorem pair_injective (k : ℕ) : Function.Injective (fun t ↦ (source t, target t k)) := by
  intro t u he
  have hh := congrArg Prod.fst he
  dsimp [source] at hh
  omega

theorem pairs_card (m k : ℕ) (hB : width k ≤ m) : (pairs m k).card = m - width k := by
  rw [pairs, card_image_of_injective _ (pair_injective k), centres, Nat.card_Ico]
  omega

theorem pairs_dyadic (m k : ℕ) (hB : width k ≤ m) {p : ℕ × ℕ} (hp : p ∈ pairs m k) :
    p.1 ∈ dyadicBlock (6 * m) ∧ p.2 ∈ dyadicBlock (6 * m) := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
  obtain ⟨hlo, hhi⟩ := mem_Ico.mp ht
  simp only [dyadicBlock, mem_Ico]
  dsimp [source, target]
  omega

theorem pairs_subset (m k : ℕ) (hB : width k ≤ m) (hlarge : 5 * (width k) ^ 4 < 3 * m) :
    pairs m k ⊆ population (6 * m) k := by
  classical
  intro p hp
  apply mem_filter.mpr
  refine ⟨mem_product.mpr (pairs_dyadic m k hB hp), ?_⟩
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
  exact ShiftedAlignmentRadius.narrow_nonalignment t k
    (hlarge.trans_le (mem_Ico.mp ht).1)

theorem pairs_enlarged_aligned (m k : ℕ) (hk : 1 ≤ k) {p : ℕ × ℕ}
    (hp : p ∈ pairs m k) : CompressedTargetAlignment.Aligned 2 p.1 p.2 (3 * k) := by
  obtain ⟨t, _ht, rfl⟩ := mem_image.mp hp
  exact ShiftedAlignmentRadius.enlarged_alignment t k hk

theorem weight_nonneg (H k : ℕ) (p : ℕ × ℕ) : 0 ≤ weight H k p := by
  exact sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

theorem pair_weight_lower {H : ℕ} (hH : 3 ≤ H) (t k : ℕ) :
    (2 : ℝ) ^ (k - 1) - 1 ≤ weight H k (source t, target t k) := by
  exact sub_le_sub_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (loss_lower hH t k)) 1

theorem total_lower {H : ℕ} (hH : 3 ≤ H) (m k : ℕ) (hB : width k ≤ m)
    (hlarge : 5 * (width k) ^ 4 < 3 * m) :
    ((m : ℝ) - width k) * ((2 : ℝ) ^ (k - 1) - 1) ≤ total (6 * m) H k := by
  calc
    _ = ∑ _p ∈ pairs m k, ((2 : ℝ) ^ (k - 1) - 1) := by
      rw [sum_const, nsmul_eq_mul, pairs_card m k hB, Nat.cast_sub hB]
    _ ≤ ∑ p ∈ pairs m k, weight H k p := by
      apply sum_le_sum
      intro p hp
      obtain ⟨t, _ht, rfl⟩ := mem_image.mp hp
      exact pair_weight_lower hH t k
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (pairs_subset m k hB hlarge)
      (fun p _ _ ↦ weight_nonneg H k p)

end PaperP1.ShiftedAsymmetricPopulation
