module

public import PaperP1.Affine.CompatibleFullSupport

/-! # Positive centered mass from the actual private-rank profile -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

open Finset PaperP1.SubspaceFamilyRank

variable {V ι : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [∀ i, Fintype (S i)]

theorem private_profile_centered_lower (A : Finset ι) (a : V) :
    (1 - ∑ i : A, (2 ^ privateRank S A i.val : ℝ) / (2 ^ Module.finrank 𝔽₂ (S i.val) : ℝ)) *
      effectiveJointMoment (fun i : A ↦ S i.val) (fun _ ↦ a) ≤
        effectiveCenteredMoment (fun i : A ↦ S i.val) (fun _ ↦ a) := by
  rw [compatible_centered_count, compatible_joint_count]
  calc
    _ = (∏ i : A, effectiveRate (S i.val)) * ((2 ^ relativeNullityOn S A : ℝ) *
        (1 - ∑ i : A, (2 ^ privateRank S A i.val : ℝ) / (2 ^ Module.finrank 𝔽₂ (S i.val) : ℝ))) := by
      unfold relativeNullityOn
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (fullSupport_profile_lower S A)
      (effectiveRate_product_nonneg (fun i : A ↦ S i.val))

omit [Fintype V] [∀ i, Fintype (S i)] in
theorem private_loss_sum_le (A : Finset ι) (L t : ℕ)
    (hrank : ∀ i ∈ A, Module.finrank 𝔽₂ (S i) = L) (hstop : ∀ i ∈ A, privateRank S A i < t) :
    (∑ i : A, (2 ^ privateRank S A i.val : ℝ) / (2 ^ Module.finrank 𝔽₂ (S i.val) : ℝ)) ≤
      (A.card : ℝ) * (2 ^ L : ℝ)⁻¹ * 2 ^ (t - 1) := by
  calc
    _ ≤ ∑ _i : A, (2 ^ L : ℝ)⁻¹ * 2 ^ (t - 1) := by
      apply sum_le_sum
      intro i _
      rw [hrank i.val i.property]
      have hpow : (2 ^ privateRank S A i.val : ℝ) ≤ 2 ^ (t - 1) :=
        pow_le_pow_right₀ (by norm_num) (by have h := hstop i.val i.property; omega)
      calc
        _ ≤ (2 ^ (t - 1) : ℝ) / (2 ^ L : ℝ) := div_le_div_of_nonneg_right hpow (by positivity)
        _ = _ := by ring
    _ = _ := by simp; ring

theorem privateRank_centered_lower_sharp (A : Finset ι) (a : V) (L t : ℕ)
    (hrank : ∀ i ∈ A, Module.finrank 𝔽₂ (S i) = L) (hstop : ∀ i ∈ A, privateRank S A i < t) :
    (1 - (A.card : ℝ) * (2 ^ L : ℝ)⁻¹ * 2 ^ (t - 1)) *
      effectiveJointMoment (fun i : A ↦ S i.val) (fun _ ↦ a) ≤
        effectiveCenteredMoment (fun i : A ↦ S i.val) (fun _ ↦ a) := by
  have hsum := private_loss_sum_le S A L t hrank hstop
  have hq := compatible_joint_nonneg (fun i : A ↦ S i.val) a
  exact (mul_le_mul_of_nonneg_right (by linarith) hq).trans (private_profile_centered_lower S A a)

theorem privateRank_centered_lower (A : Finset ι) (a : V) (L t : ℕ)
    (hrank : ∀ i ∈ A, Module.finrank 𝔽₂ (S i) = L) (hstop : ∀ i ∈ A, privateRank S A i < t) :
    (1 - (A.card : ℝ) * (2 ^ L : ℝ)⁻¹ * 2 ^ t) *
      effectiveJointMoment (fun i : A ↦ S i.val) (fun _ ↦ a) ≤
        effectiveCenteredMoment (fun i : A ↦ S i.val) (fun _ ↦ a) := by
  have hpow : (2 ^ (t - 1) : ℝ) ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hfactor : (A.card : ℝ) * (2 ^ L : ℝ)⁻¹ * 2 ^ (t - 1) ≤
      (A.card : ℝ) * (2 ^ L : ℝ)⁻¹ * 2 ^ t := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hq := compatible_joint_nonneg (fun i : A ↦ S i.val) a
  exact (mul_le_mul_of_nonneg_right (by linarith) hq).trans
    (privateRank_centered_lower_sharp S A a L t hrank hstop)

end PaperP1.Affine
