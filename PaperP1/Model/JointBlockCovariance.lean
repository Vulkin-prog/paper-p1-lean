module

public import PaperP1.Model.HomogeneousRunMass
public import PaperP1.Model.JointMonotonicity

/-! # Actual block covariances are controlled by the full intersection rank, including incompatible unions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.JointBlockCovariance

open Finset PaperP1.Arithmetic PaperP1.Model.InfiniteStarts PaperP1.SubspaceFamilyRank
  PaperP1.FiniteFamilyEnumeration

def intersectionRank (L : ℕ) (e f : Finset ℕ) : ℕ := Module.finrank F₂
  ↥(span (fun x ↦ squareClassSpace x L) e ⊓ span (fun x ↦ squareClassSpace x L) f)

theorem zero_or_homogeneous (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    infiniteJointMoment L I = 0 ∨ infiniteJointMoment L I = HomogeneousRunMass.probability L I := by
  let x := centres I rfl
  have hs : FiniteFamilyEnumeration.tupleSet x = I := centres_tupleSet I rfl
  have hj := JointTupleSupport.prescribed_eq_support x hL
  rw [hs] at hj
  rcases PrescribedTupleRank.joint_zero_or_rank (fun _ ↦ Affine.startRhs L) x with hz | hr
  · exact Or.inl (hj.symm.trans hz)
  · right
    have hhom := HomogeneousRunMass.tuple_rank (L := L) x
    have heq : PrescribedTupleMass.joint L (fun _ ↦ Affine.startRhs L) x = PrescribedTupleMass.joint L (fun _ ↦ 0) x := hr.trans hhom.symm
    rw [hj, HomogeneousRunMass.tuple_probability, hs] at heq
    exact heq

theorem positive_eq_homogeneous (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hI : 0 < infiniteJointMoment L I) :
    infiniteJointMoment L I = HomogeneousRunMass.probability L I := by
  rcases zero_or_homogeneous L hL I with hz | heq
  · exact False.elim (hI.ne' hz)
  · exact heq

theorem homogeneous_union_factor (L : ℕ) (e f : Finset ℕ) :
    HomogeneousRunMass.probability L (e ∪ f) = (2 ^ intersectionRank L e f : ℝ) *
      HomogeneousRunMass.probability L e * HomogeneousRunMass.probability L f := by
  have hfin₁ := RetainedNullity.span_finite (fun x ↦ squareClassSpace x L) e
  have hfin₂ := RetainedNullity.span_finite (fun x ↦ squareClassSpace x L) f
  have hrank : rank (fun x ↦ squareClassSpace x L) (e ∪ f) + intersectionRank L e f =
      rank (fun x ↦ squareClassSpace x L) e + rank (fun x ↦ squareClassSpace x L) f := by
    rw [rank, RetainedNullity.span_union]
    exact Submodule.finrank_sup_add_finrank_inf_eq _ _
  have hp := congrArg (fun k : ℕ ↦ (2 : ℝ) ^ k) hrank
  simp only [pow_add] at hp
  rw [HomogeneousRunMass.probability_rank, HomogeneousRunMass.probability_rank, HomogeneousRunMass.probability_rank]
  field_simp
  nlinarith only [hp]

theorem actual_covariance_bound (L : ℕ) (hL : 0 < L) (e f : Finset ℕ)
    (he : 0 < infiniteJointMoment L e) (hf : 0 < infiniteJointMoment L f) :
    |infiniteJointMoment L (e ∪ f) - infiniteJointMoment L e * infiniteJointMoment L f| ≤
      (2 ^ intersectionRank L e f : ℝ) * (infiniteJointMoment L e * infiniteJointMoment L f) := by
  have hprod : 0 ≤ infiniteJointMoment L e * infiniteJointMoment L f := mul_nonneg he.le hf.le
  have hupper : infiniteJointMoment L (e ∪ f) ≤
      (2 ^ intersectionRank L e f : ℝ) * (infiniteJointMoment L e * infiniteJointMoment L f) := by
    calc
      _ ≤ HomogeneousRunMass.probability L (e ∪ f) := HomogeneousRunMass.actual_joint_le L hL _
      _ = _ := by rw [homogeneous_union_factor, ← positive_eq_homogeneous L hL e he,
        ← positive_eq_homogeneous L hL f hf, mul_assoc]
  have hboost : (1 : ℝ) ≤ 2 ^ intersectionRank L e f := one_le_pow₀ (by norm_num)
  have hprodle := mul_le_mul_of_nonneg_right hboost hprod
  have hnonneg := infiniteJointMoment_nonneg L (e ∪ f)
  exact abs_le.mpr ⟨by nlinarith only [hprodle, hnonneg], by nlinarith only [hupper, hprod]⟩

end PaperP1.JointBlockCovariance
