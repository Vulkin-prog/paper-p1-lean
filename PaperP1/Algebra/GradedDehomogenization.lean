module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Finiteness.Basic

/-! # Degree-one dehomogenization and finiteness of actual chart ring maps -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedDehomogenization

open HomogeneousLocalization DirectSum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (G : ℕ → σ) [GradedRing G] {b : A} (hb : b ∈ G 1)

def component (n : ℕ) : G n →+ Away G b where
  toFun x := Away.mk G hb n x (by simpa only [smul_eq_mul, mul_one] using x.property)
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp [Away.val_mk, val_zero, Localization.mk_zero]
  map_add' x y := by
    apply HomogeneousLocalization.val_injective
    simp only [Away.val_mk, val_add]
    change Localization.mk ((x : A) + (y : A)) _ = _
    exact (Localization.add_mk_self _ _ _).symm

theorem component_one : component G hb 0 ⟨1, SetLike.one_mem_graded G⟩ = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [component, Away.val_mk, val_one]

theorem component_mul {n m : ℕ} (x : G n) (y : G m) :
    component G hb (n + m) ⟨(x : A) * (y : A), SetLike.mul_mem_graded x.property y.property⟩ =
      component G hb n x * component G hb m y := by
  apply HomogeneousLocalization.val_injective
  simp [component, Away.val_mk, val_mul, Localization.mk_mul, pow_add]

def map : A →+* Away G b :=
  (DirectSum.toSemiring (component G hb) (component_one G hb)
    (component_mul G hb)).comp (DirectSum.decomposeRingEquiv G).toRingHom

theorem map_homogeneous (n : ℕ) (x : A) (hx : x ∈ G n) :
    map G hb x = Away.mk G hb n x (by simpa only [smul_eq_mul, mul_one] using hx) := by
  change DirectSum.toSemiring (component G hb) (component_one G hb) (component_mul G hb) (decompose G x) = _
  rw [DirectSum.decompose_of_mem G hx, DirectSum.toSemiring_of]
  rfl

theorem map_surjective : Function.Surjective (map G hb) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective G hb z
  exact ⟨a, map_homogeneous G hb n a (by simpa only [smul_eq_mul, mul_one] using ha)⟩

variable {B τ : Type*} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {H : ℕ → τ} [GradedRing H]

theorem map_natural (f : G →+*ᵍ H) :
    (Away.map f b).comp (map G hb) = (map H (f.map_mem hb)).comp f.toRingHom := by
  classical
  apply RingHom.ext
  intro x
  rw [← DirectSum.sum_support_decompose G x]
  simp only [map_sum, RingHom.comp_apply]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [map_homogeneous G hb n _ (decompose G x n).property, Away.map_mk,
    map_homogeneous H (f.map_mem hb) n _ (f.map_mem (decompose G x n).property)]
  rfl

include hb in
theorem away_map_finite (f : G →+*ᵍ H) (hf : f.toRingHom.Finite) : (Away.map f b).Finite := by
  have hcomp := (RingHom.Finite.of_surjective (map H (f.map_mem hb))
    (map_surjective H (f.map_mem hb))).comp hf
  rw [← map_natural G hb f] at hcomp
  exact RingHom.Finite.of_comp_finite hcomp

end PaperP1.GradedDehomogenization
