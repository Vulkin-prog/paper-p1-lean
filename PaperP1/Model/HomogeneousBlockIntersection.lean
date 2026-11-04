module

public import PaperP1.Model.HomogeneousRunMass
public import PaperP1.Model.AsymmetricJointWeight

/-! # Exact homogeneous block intersection and the actual asymmetric loss

All homogeneous probabilities refer to the original prime-sign measure with
zero affine target. No compatibility, regularity or disjointness is needed for
the exact intersection identity.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousBlockIntersection

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.HomogeneousRunMass
  PaperP1.SubspaceFamilyRank PaperP1.AsymmetricEvenLoss

theorem exact (L : ℕ) (E A : Finset ℕ) :
    probability L (E ∪ A) = probability L E * probability L A *
      (2 ^ Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) E ⊓
        span (fun x ↦ squareClassSpace x L) A) : ℝ) := by
  let S := fun x ↦ squareClassSpace x L
  let : Fintype (span S E) := MinimalRelativeRelations.spanFintype S E
  let : Fintype (span S A) := MinimalRelativeRelations.spanFintype S A
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (span S E) (span S A)
  rw [← RetainedNullity.span_union S E A] at hdim
  have hp : (2 ^ rank S E : ℝ) * (2 ^ rank S A : ℝ) =
      (2 ^ rank S (E ∪ A) : ℝ) * (2 ^ Module.finrank F₂ ↥(span S E ⊓ span S A) : ℝ) := by
    rw [← pow_add, ← pow_add]
    congr 1
    exact hdim.symm
  rw [probability_rank, probability_rank, probability_rank]
  change (2 ^ rank S (E ∪ A) : ℝ)⁻¹ = (2 ^ rank S E : ℝ)⁻¹ * (2 ^ rank S A : ℝ)⁻¹ * _
  field_simp
  exact hp

theorem upper_loss (L H : ℕ) (E U : Finset ℕ) (z : ℕ)
    (hspace : span (fun x ↦ squareClassSpace x L) E = FiniteEvenSquareClasses.space U) :
    probability L (E ∪ {z}) ≤ probability L E * probability L {z} * (2 ^ loss H U z L : ℝ) := by
  have hh := exact L E {z}
  have hsingle : span (fun x ↦ squareClassSpace x L) {z} = squareClassSpace z L := by simp [span]
  rw [hsingle, hspace] at hh
  rw [hh]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (AsymmetricIntersectionTransport.intersection_le_loss H U z L))
    (mul_nonneg (probability_pos L E).le (probability_pos L {z}).le)

theorem crossing (L H : ℕ) (E U : Finset ℕ) (z : ℕ)
    (hspace : span (fun x ↦ squareClassSpace x L) E = FiniteEvenSquareClasses.space U)
    (hcross : 0 < Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) E ⊓ squareClassSpace z L)) :
    probability L (E ∪ {z}) ≤ 2 * (probability L E * probability L {z}) *
      ((2 ^ loss H U z L : ℝ) - 1) := by
  have hdim := AsymmetricIntersectionTransport.intersection_le_loss H U z L
  rw [hspace] at hcross
  have hδ : 1 ≤ loss H U z L := by omega
  have hpow : (2 : ℝ) ≤ 2 ^ loss H U z L := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hδ
  have hpower : (2 ^ loss H U z L : ℝ) ≤ 2 * ((2 ^ loss H U z L : ℝ) - 1) := by linarith only [hpow]
  calc
    _ ≤ (probability L E * probability L {z}) * (2 ^ loss H U z L : ℝ) := upper_loss L H E U z hspace
    _ ≤ (probability L E * probability L {z}) * (2 * ((2 ^ loss H U z L : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hpower (mul_nonneg (probability_pos L E).le (probability_pos L {z}).le)
    _ = _ := by ring

end PaperP1.HomogeneousBlockIntersection
