module

public import PaperP1.Affine.FullSupportCounting
public import PaperP1.Affine.PartitionMoments

/-! # Compatible affine families: actual moments and the full-support relation count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

open Finset PaperP1.SubspaceFamilyRank

variable {V ι : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [∀ i, Fintype (S i)]

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
theorem affineTupleSign_common (a : V) (s : (i : ι) → S i) (hs : relationAddition S s = 0) :
    affineTupleSign S (fun _ ↦ a) s = 1 := by
  classical
  unfold affineTupleSign
  rw [realCharacter_sum, ← relationAddition_apply, hs, realCharacter_zero]

variable [Fintype V]

theorem compatible_centered_count (a : V) :
    effectiveCenteredMoment S (fun _ ↦ a) =
      (∏ i, effectiveRate (S i)) * (fullSupportRelations S).card := by
  classical
  rw [effectiveCenteredMoment, effective_full_support_formula]
  congr 1
  have hterm (s : (i : ι) → S i) :
      (if IsFullSupportRelation S s then affineTupleSign S (fun _ ↦ a) s else 0) =
        if IsFullSupportRelation S s then (1 : ℝ) else 0 := by
    by_cases hs : IsFullSupportRelation S s
    · rw [ite_eq_left hs, ite_eq_left hs, affineTupleSign_common S a s hs.2]
    · simp only [hs, ite_false]
  simp_rw [hterm]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  rfl

theorem compatible_joint_count (a : V) :
    effectiveJointMoment S (fun _ ↦ a) = (∏ i, effectiveRate (S i)) * (2 ^ relativeNullity S : ℝ) := by
  classical
  rw [effective_joint_spectral]
  congr 1
  unfold spectralCoefficient
  have hterm (s : (i : ι) → S i) :
      (if HasFrequencyRelation S (fun _ _ ↦ True) s then affineTupleSign S (fun _ ↦ a) s else 0) =
        if relationAddition S s = 0 then (1 : ℝ) else 0 := by
    by_cases hs : relationAddition S s = 0
    · simp only [HasFrequencyRelation, hs, and_self, implies_true, ite_true,
        affineTupleSign_common S a s hs]
    · simp only [HasFrequencyRelation, hs, and_false, ite_false]
  simp_rw [hterm]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  have hcard : (univ.filter fun s : (i : ι) → S i ↦ relationAddition S s = 0).card =
      2 ^ relativeNullity S := by
    let : AddCommGroup (LinearMap.ker (relationAddition S)) :=
      Submodule.addCommGroup (R := 𝔽₂) (M := (i : ι) → S i) _
    let : Fintype (LinearMap.ker (relationAddition S)) := Fintype.ofFinite _
    calc
      _ = Fintype.card (LinearMap.ker (relationAddition S)) := by
        symm
        simpa only [LinearMap.mem_ker] using (Fintype.card_subtype
          (fun s : (i : ι) → S i ↦ s ∈ LinearMap.ker (relationAddition S)))
      _ = _ := card_eq_two_pow_finrank
  exact_mod_cast hcard

theorem compatible_centered_nonneg (a : V) : 0 ≤ effectiveCenteredMoment S (fun _ ↦ a) := by
  rw [compatible_centered_count]
  exact mul_nonneg (effectiveRate_product_nonneg S) (Nat.cast_nonneg _)

theorem compatible_joint_nonneg (a : V) : 0 ≤ effectiveJointMoment S (fun _ ↦ a) := by
  rw [compatible_joint_count]
  exact mul_nonneg (effectiveRate_product_nonneg S) (by positivity)

end PaperP1.Affine
