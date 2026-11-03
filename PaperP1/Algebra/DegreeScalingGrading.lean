module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! # Projection and homogeneous ideal pullback for a positive scaling of degrees -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DegreeScalingGrading

open DirectSum

variable {F A B : Type*} [CommRing F] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B} [GradedAlgebra G] [GradedAlgebra H]
  (D : ℕ) (hD : 0 < D) (f : G →+*ᵍ (fun n ↦ H (n * D)))

include hD in
theorem proj_map (n : ℕ) (x : A) :
    f (GradedAlgebra.proj G n x) = GradedAlgebra.proj H (n * D) (f x) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose G x]
  conv_rhs => rw [← DirectSum.sum_support_decompose G x]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hnm : n = m
  · subst m
    rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same G (decompose G x n).property,
      GradedAlgebra.proj_apply]
    exact (DirectSum.decompose_of_mem_same H (f.map_mem (decompose G x n).property)).symm
  · have hmn : m ≠ n := Ne.symm hnm
    have hmnD : m * D ≠ n * D := fun h ↦ hmn (mul_right_cancel₀ (Nat.ne_of_gt hD) h)
    rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne G (decompose G x m).property hmn,
      map_zero, GradedAlgebra.proj_apply]
    exact (DirectSum.decompose_of_mem_ne H (f.map_mem (decompose G x m).property) hmnD).symm

def comap (I : HomogeneousIdeal H) : HomogeneousIdeal G where
  __ := I.toIdeal.comap f.toRingHom
  is_homogeneous' n a ha := by
    change f (GradedAlgebra.proj G n a) ∈ I.toIdeal
    rw [proj_map D hD f]
    exact I.is_homogeneous' (n * D) ha

theorem comap_toIdeal (I : HomogeneousIdeal H) :
    (comap D hD f I).toIdeal = I.toIdeal.comap f.toRingHom := rfl

end PaperP1.DegreeScalingGrading
