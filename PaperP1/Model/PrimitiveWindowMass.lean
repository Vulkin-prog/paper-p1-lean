module

public import PaperP1.Affine.PrimitiveNullity
public import PaperP1.Model.FamilyIndependentMass
public import PaperP1.Model.LocalRunRank
public import PaperP1.Model.SquareClassFourier
public import PaperP1.Model.CanonicalRunComponents

/-! # Primitive effective window weight is at most 2^L times its exact independent weight -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveWindowMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Affine PaperP1.ConnectedWindowFamilies

def weight (L : ℕ) (I : Finset ℕ) : ℝ :=
  (∏ x ∈ I, infiniteMarginal x L) * (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ)

def mass (F : Finset (Finset ℕ)) (L : ℕ) : ℝ := ∑ I ∈ F, weight L I

theorem weight_nonneg (L : ℕ) (I : Finset ℕ) : 0 ≤ weight L I :=
  mul_nonneg (prod_nonneg fun x _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    (pow_nonneg (by norm_num) _)

theorem primitive_nullity_le (L : ℕ) (I : Finset ℕ) (hI : I.Nonempty)
    (hprim : Primitive L I) (hpos : ∀ x ∈ I, 0 < x) :
    relativeNullityOn (fun x ↦ squareClassSpace x L) I ≤ L := by
  obtain ⟨x, hx⟩ := hI
  exact (PrimitiveNullity.minimal_bound _ I hprim.2 x hx).trans
    (LocalRunRank.squareClass_rank_le x L (hpos x hx))

theorem primitive_weight_le (L : ℕ) (I : Finset ℕ) (hI : I.Nonempty)
    (hprim : Primitive L I) (hpos : ∀ x ∈ I, 0 < x) :
    weight L I ≤ (∏ x ∈ I, infiniteMarginal x L) * (2 ^ L : ℝ) := by
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (primitive_nullity_le L I hI hprim hpos))
    (prod_nonneg fun x _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)

theorem primitive_mass_le (F : Finset (Finset ℕ)) (L : ℕ)
    (hF : ∀ I ∈ F, I.Nonempty ∧ Primitive L I ∧ ∀ x ∈ I, 0 < x) :
    mass F L ≤ (2 ^ L : ℝ) * FamilyIndependentMass.independentMass F L := by
  unfold mass FamilyIndependentMass.independentMass
  rw [mul_sum]
  apply sum_le_sum
  intro I hI
  simpa only [mul_comm] using primitive_weight_le L I (hF I hI).1 (hF I hI).2.1 (hF I hI).2.2

theorem joint_le_weight (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    infiniteJointMoment L I ≤ weight L I := by
  by_cases hq : 0 < infiniteJointMoment L I
  · exact (infiniteJointMoment_exact_of_pos (I.sup fun x ↦ x + L) L I hL
      (fun _x hx ↦ le_sup (f := fun x ↦ x + L) hx) hq).le
  · exact (le_of_not_gt hq).trans (weight_nonneg L I)

theorem centered_le_weight (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hI : I.Nonempty)
    (hp : ∀ x ∈ I, 0 < infiniteMarginal x L) :
    |infiniteCenteredCoefficient L I| ≤ weight L I := by
  classical
  obtain ⟨i, hi⟩ := hI
  let : Nonempty I := ⟨⟨i, hi⟩⟩
  let M := I.sup fun x ↦ x + L
  have hcut : ∀ x : I, x.val + L ≤ M := fun x ↦ le_sup (f := fun x ↦ x + L) x.property
  have h := squareClass_centered_moment_coarse_bound M L (fun x : I ↦ x.val) hL hcut
    (fun x ↦ hp x.val x.property)
  rw [← infiniteCenteredCoefficient_eq_family_subtype] at h
  have hprod : (∏ x : I, infiniteMarginal x.val L) = ∏ x ∈ I, infiniteMarginal x L := by
    rw [univ_eq_attach]
    exact prod_attach I (fun x ↦ infiniteMarginal x L)
  rw [hprod] at h
  exact h

end PaperP1.PrimitiveWindowMass
