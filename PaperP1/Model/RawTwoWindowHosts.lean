module

public import PaperP1.Arithmetic.LargeAnchorPairs
public import PaperP1.Model.FiniteRademacher

/-! # Unrestricted raw two-window relations have an actual large-kernel anchor

Neither block is required to select an even number of vertices. Local
relations and diagonal pairs are included. This is the full raw-value
population, not the even effective relation population of the half-count.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawTwoWindowHosts

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.LargeOddKernel
  PaperP1.SelectedKernelWitness

local instance rawTwoWindowHostsDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

def Related (x y B : ℕ) : Prop :=
  ∃ w v : Fin B → F₂, (w ≠ 0 ∨ v ≠ 0) ∧
    (∑ i, w i • parityVec (x - 1 + i.val)) +
      (∑ i, v i • parityVec (y - 1 + i.val)) = 0

def hosts (N B : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun p ↦ Related p.1 p.2 B

theorem nonzero_coordinate {B : ℕ} {w : Fin B → F₂} (hw : w ≠ 0) : ∃ i, w i ≠ 0 := by
  by_contra hn
  apply hw
  funext i
  have hz : w i = 0 := by
    by_contra h
    exact hn ⟨i, h⟩
  exact hz

theorem anchor_cutoff (B n : ℕ) : (1 / 2 : ℝ) < largeOddKernel B n := by
  have h : (1 : ℝ) ≤ largeOddKernel B n := by
    exact_mod_cast PaperP1.SmallPrimeBudget.largeOddKernel_pos B n
  linarith only [h]

theorem related_oriented_anchor {x y B : ℕ} (h : Related x y B) :
    (∃ i : Fin B, AnchoredRelation (x - 1) (y - 1) B i) ∨
      (∃ i : Fin B, AnchoredRelation (y - 1) (x - 1) B i) := by
  obtain ⟨w, v, hwv, hrel⟩ := h
  rcases hwv with hw | hv
  · obtain ⟨i, hi⟩ := nonzero_coordinate hw
    exact Or.inl ⟨i, w, v, hi, hrel⟩
  · obtain ⟨i, hi⟩ := nonzero_coordinate hv
    exact Or.inr ⟨i, v, w, hi, by simpa only [add_comm] using hrel⟩

theorem hosts_subset_anchored (N B : ℕ) :
    hosts N B ⊆ PaperP1.LargeAnchorPairs.bothPairs N B (1 / 2) := by
  intro p hp
  obtain ⟨hp, hrel⟩ := mem_filter.mp hp
  obtain ⟨hx, hy⟩ := mem_product.mp hp
  rcases related_oriented_anchor hrel with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩,
      i, anchor_cutoff B _, hi⟩)
  · apply mem_union_right
    exact mem_image.mpr ⟨p.swap, mem_filter.mpr ⟨mem_product.mpr ⟨hy, hx⟩,
      i, anchor_cutoff B _, hi⟩, Prod.swap_swap p⟩

def growthConstant : ℝ := 2 + PaperP1.PowerSeriesTail.constant (1 + 1 / 2)

theorem growthConstant_nonneg : 0 ≤ growthConstant := by
  unfold growthConstant PaperP1.PowerSeriesTail.constant
  positivity

theorem finite_bound {N B : ℕ} (hN : 2 ≤ N) (hB : 1 ≤ B) (hBN : B ≤ N) :
    ((hosts N B).card : ℝ) ≤
      8 * B * N * Real.sqrt (3 * N) * Real.exp (growthConstant * Real.sqrt B) := by
  have hc : ((hosts N B).card : ℝ) ≤
      (PaperP1.LargeAnchorPairs.bothPairs N B (1 / 2)).card := by
    exact_mod_cast card_le_card (hosts_subset_anchored N B)
  have h := PaperP1.LargeAnchorPairs.finite_exp_bound (1 / 2) (1 / 2)
    hN hB hBN (by norm_num) (by norm_num) le_rfl
  have he : (-1 : ℝ) / 2 + 1 / 2 = 0 := by ring
  have he' : 1 - (1 / 2 : ℝ) = 1 / 2 := by ring
  rw [he, Real.rpow_zero, mul_one, he', ← Real.sqrt_eq_rpow] at h
  have hfactor : 2 * Real.sqrt (B : ℝ) + PaperP1.PowerSeriesTail.constant (1 + 1 / 2) * Real.sqrt B =
      growthConstant * Real.sqrt B := by unfold growthConstant; ring
  rw [hfactor] at h
  exact hc.trans h

end PaperP1.RawTwoWindowHosts
