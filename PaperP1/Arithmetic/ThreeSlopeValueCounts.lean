module

public import PaperP1.Arithmetic.ThreeSlopeProgressions
public import Mathlib.Algebra.BigOperators.Fin

/-! # Exact pair, triple and union cardinalities of the extremal normalized triple -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeSlopeValueCounts

open Finset PaperP1.Arithmetic PaperP1.NormalizedWindowSets PaperP1.PrivateNormalizedFamilies
  PaperP1.ThreeSlopeProgressions

def pairFloor (L d : ℕ) : ℕ := (L - 1) / d
def nullity (L : ℕ) : ℕ := pairFloor L 6 + pairFloor L 3 + pairFloor L 5 - pairFloor L 15

theorem image_card (T d M : ℕ) (hd : 0 < d) :
    ((range M).image (fun m ↦ T + d * m)).card = M := by
  rw [card_image_of_injective _ (fun _ _ hh ↦ Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel hh)), card_range]

theorem pair_zero_one {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L) :
    (normalized (step 0) (centres t 0) L ∩ normalized (step 1) (centres t 1) L).card = pairFloor L 6 + 1 := by
  rw [normalized_progression ht, normalized_progression ht]
  change (progression (60 * t) 6 L ∩ progression (60 * t) 5 L).card = _
  rw [inter_six_five (by omega) hL, image_card _ _ _ (by omega)]
  rfl

theorem pair_zero_two {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L) :
    (normalized (step 0) (centres t 0) L ∩ normalized (step 2) (centres t 2) L).card = pairFloor L 3 + 1 := by
  rw [normalized_progression ht, normalized_progression ht]
  change (progression (60 * t) 6 L ∩ progression (60 * t) 4 L).card = _
  rw [inter_six_four (by omega) hL, image_card _ _ _ (by omega)]
  rfl

theorem pair_one_two {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L) :
    (normalized (step 1) (centres t 1) L ∩ normalized (step 2) (centres t 2) L).card = pairFloor L 5 + 1 := by
  rw [normalized_progression ht, normalized_progression ht]
  change (progression (60 * t) 5 L ∩ progression (60 * t) 4 L).card = _
  rw [inter_five_four (by omega) hL, image_card _ _ _ (by omega)]
  rfl

theorem triple_card {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L) :
    ((normalized (step 0) (centres t 0) L ∩ normalized (step 1) (centres t 1) L) ∩
      normalized (step 2) (centres t 2) L).card = pairFloor L 15 + 1 := by
  rw [normalized_progression ht, normalized_progression ht, normalized_progression ht]
  change ((progression (60 * t) 6 L ∩ progression (60 * t) 5 L) ∩ progression (60 * t) 4 L).card = _
  rw [inter_three (by omega) hL, image_card _ _ _ (by omega)]
  rfl

theorem union_three (t L : ℕ) :
    valueUnion step (centres t) L =
      (normalized (step 0) (centres t 0) L ∪ normalized (step 1) (centres t 1) L) ∪
        normalized (step 2) (centres t 2) L := by
  have hu : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [valueUnion, hu]
  simp only [biUnion_insert, singleton_biUnion, union_assoc]

theorem union_card_identity {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L) :
    (valueUnion step (centres t) L).card + pairFloor L 6 + pairFloor L 3 + pairFloor L 5 + 2 =
      3 * (L + 1) + pairFloor L 15 := by
  let A := normalized (step 0) (centres t 0) L
  let B := normalized (step 1) (centres t 1) L
  let C := normalized (step 2) (centres t 2) L
  have hA : A.card = L + 1 := card_normalized (step_pos _) (by have hh := centres_ge_two ht 0; omega)
  have hB : B.card = L + 1 := card_normalized (step_pos _) (by have hh := centres_ge_two ht 1; omega)
  have hC : C.card = L + 1 := card_normalized (step_pos _) (by have hh := centres_ge_two ht 2; omega)
  have h01 : (A ∩ B).card = pairFloor L 6 + 1 := pair_zero_one ht hL
  have h02 : (A ∩ C).card = pairFloor L 3 + 1 := pair_zero_two ht hL
  have h12 : (B ∩ C).card = pairFloor L 5 + 1 := pair_one_two ht hL
  have h012 : ((A ∩ B) ∩ C).card = pairFloor L 15 + 1 := triple_card ht hL
  have h₁ := card_union_add_card_inter A B
  have h₂ := card_union_add_card_inter (A ∪ B) C
  rw [union_inter_distrib_right] at h₂
  have h₃ := card_union_add_card_inter (A ∩ C) (B ∩ C)
  have heq : (A ∩ C) ∩ (B ∩ C) = (A ∩ B) ∩ C := by ext n; simp only [mem_inter]; tauto
  rw [heq] at h₃
  have hu : (valueUnion step (centres t) L).card = ((A ∪ B) ∪ C).card := congrArg card (union_three t L)
  omega

theorem nullity_rank_identity {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L) :
    (valueUnion step (centres t) L).card - 1 + nullity L = 3 * L := by
  have hu := union_card_identity ht hL
  have hnon : 1 ≤ (valueUnion step (centres t) L).card := card_pos.mpr
    ⟨60 * t, normalized_subset step (centres t) L 0 (common_mem ht (by omega) 0)⟩
  have hdiv : pairFloor L 15 ≤ pairFloor L 3 := by
    unfold pairFloor
    omega
  unfold nullity
  omega

theorem nullity_bounds (L : ℕ) (hL : 1 ≤ L) :
    (19 / 30 : ℝ) * L - 4 ≤ (nullity L : ℝ) ∧ (nullity L : ℝ) ≤ (19 / 30 : ℝ) * L + 1 := by
  have hdiv : pairFloor L 15 ≤ pairFloor L 3 := by unfold pairFloor; omega
  have hnat : nullity L + pairFloor L 15 = pairFloor L 6 + pairFloor L 3 + pairFloor L 5 := by
    unfold nullity
    omega
  have hreal : (nullity L : ℝ) + pairFloor L 15 = pairFloor L 6 + pairFloor L 3 + pairFloor L 5 := by exact_mod_cast hnat
  have h6 : (6 : ℝ) * pairFloor L 6 ≤ (L : ℝ) - 1 ∧ (L : ℝ) - 1 < 6 * (pairFloor L 6 + 1) := by
    have hh : 6 * pairFloor L 6 ≤ L - 1 ∧ L - 1 < 6 * (pairFloor L 6 + 1) := by unfold pairFloor; omega
    exact_mod_cast hh
  have h3 : (3 : ℝ) * pairFloor L 3 ≤ (L : ℝ) - 1 ∧ (L : ℝ) - 1 < 3 * (pairFloor L 3 + 1) := by
    have hh : 3 * pairFloor L 3 ≤ L - 1 ∧ L - 1 < 3 * (pairFloor L 3 + 1) := by unfold pairFloor; omega
    exact_mod_cast hh
  have h5 : (5 : ℝ) * pairFloor L 5 ≤ (L : ℝ) - 1 ∧ (L : ℝ) - 1 < 5 * (pairFloor L 5 + 1) := by
    have hh : 5 * pairFloor L 5 ≤ L - 1 ∧ L - 1 < 5 * (pairFloor L 5 + 1) := by unfold pairFloor; omega
    exact_mod_cast hh
  have h15 : (15 : ℝ) * pairFloor L 15 ≤ (L : ℝ) - 1 ∧ (L : ℝ) - 1 < 15 * (pairFloor L 15 + 1) := by
    have hh : 15 * pairFloor L 15 ≤ L - 1 ∧ L - 1 < 15 * (pairFloor L 15 + 1) := by unfold pairFloor; omega
    exact_mod_cast hh
  constructor <;> linarith

end PaperP1.ThreeSlopeValueCounts
