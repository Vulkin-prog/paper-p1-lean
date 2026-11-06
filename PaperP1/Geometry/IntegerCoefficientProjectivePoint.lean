module

public import PaperP1.Algebra.WeightedHomogeneousEvaluation
public import PaperP1.Algebra.P3CoefficientFieldTransport
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! # Literal field-valued coefficient vectors give actual points of integer projective coefficient space -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerCoefficientProjectivePoint

open MvPolynomial
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F σ : Type*} [CommRing F]

def rayMap (a : σ → F) : MvPolynomial σ ℤ →+* MvPolynomial Unit F :=
  eval₂Hom (C.comp (Int.castRingHom F)) (fun i ↦ C (a i) * X ())

theorem rayMap_X (a : σ → F) (i : σ) : rayMap a (X i) = C (a i) * X () := by
  simp [rayMap]

theorem ray_homogeneous (a : σ → F) (P : MvPolynomial σ ℤ) {d : ℕ} (hP : P.IsHomogeneous d) :
    (rayMap a P).IsHomogeneous d := by
  have hh := hP.eval₂ (C.comp (Int.castRingHom F)) (fun i ↦ C (a i) * X ())
    (fun r ↦ isHomogeneous_C _ _) (fun i ↦ isHomogeneous_C_mul_X (a i) ())
  simpa only [rayMap, coe_eval₂Hom, one_mul] using hh

def gradedMap (a : σ → F) : homogeneousSubmodule σ ℤ →+*ᵍ homogeneousSubmodule Unit F where
  __ := rayMap a
  map_mem hP := ray_homogeneous a _ hP

def ideal (a : σ → F) : HomogeneousIdeal (homogeneousSubmodule σ ℤ) :=
  (⊥ : HomogeneousIdeal (homogeneousSubmodule Unit F)).comap (gradedMap a)

theorem ideal_eq_kernel (a : σ → F) : (ideal a).toIdeal = RingHom.ker (rayMap a) := rfl

theorem rayMap_aeval (a : σ → F) (P : MvPolynomial σ ℤ) :
    rayMap a P = aeval (R := F) (fun i ↦ C (a i) * X () : σ → MvPolynomial Unit F)
      (map (Int.castRingHom F) P) := by
  have he : rayMap a =
      (aeval (R := F) (fun i ↦ C (a i) * X () : σ → MvPolynomial Unit F)).toRingHom.comp
        (MvPolynomial.map (Int.castRingHom F)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [rayMap]
    · intro i
      simp [rayMap]
  exact RingHom.congr_fun he P

theorem constant_aeval (a : σ → F) (P : MvPolynomial σ F) :
    aeval (R := F) (fun i ↦ C (a i) : σ → MvPolynomial Unit F) P = C (eval a P) := by
  have he := map_eval₂Hom (RingHom.id F) a (C : F →+* MvPolynomial Unit F) P
  simpa only [aeval_eq_eval₂Hom, algebraMap_eq, eval, RingHom.comp_id] using he.symm

theorem ray_homogeneous_value (a : σ → F) (P : MvPolynomial σ ℤ) {d : ℕ}
    (hP : P.IsHomogeneous d) :
    rayMap a P = C (eval a (map (Int.castRingHom F) P)) * X () ^ d := by
  rw [rayMap_aeval]
  have he : (fun i : σ ↦ C (a i) * X () : σ → MvPolynomial Unit F) =
      (fun i : σ ↦ X () * C (a i)) := by funext i; exact mul_comm _ _
  rw [he, WeightedHomogeneousEvaluation.aeval_homogeneous_scale _ (hP.map _) (X ()) (fun i ↦ C (a i)),
    constant_aeval, mul_comm]

theorem integer_evaluation_map {L : Type*} [CommRing L] (φ : F →+* L)
    (a : σ → F) (P : MvPolynomial σ ℤ) :
    φ (eval a (map (Int.castRingHom F) P)) =
      eval (φ ∘ a) (map (Int.castRingHom L) P) := by
  have hc : φ.comp (Int.castRingHom F) = Int.castRingHom L := by ext; simp
  rw [eval₂_comp, eval₂_map, hc]
  exact (eval_map _ _ _).symm

section Field

variable {K : Type*} [Field K]

theorem ideal_prime (a : σ → K) : (ideal a).toIdeal.IsPrime := by
  rw [ideal_eq_kernel]
  exact RingHom.ker_isPrime (rayMap a)

def point (a : σ → K) (ha : a ≠ 0) : ProjectiveSpectrum (homogeneousSubmodule σ ℤ) where
  asHomogeneousIdeal := ideal a
  isPrime := ideal_prime a
  not_irrelevant_le h := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    have hx := HomogeneousIdeal.mem_irrelevant_of_mem (homogeneousSubmodule σ ℤ)
      (by decide : 0 < 1) (isHomogeneous_X ℤ i)
    have hh := h hx
    change rayMap a (X i) = 0 at hh
    rw [rayMap_X] at hh
    exact mul_ne_zero (C_ne_zero.mpr hi) (X_ne_zero ()) hh

theorem homogeneous_mem_iff (a : σ → K) (ha : a ≠ 0)
    (P : MvPolynomial σ ℤ) {d : ℕ} (hP : P.IsHomogeneous d) :
    P ∈ (point a ha).asHomogeneousIdeal ↔ eval a (map (Int.castRingHom K) P) = 0 := by
  change rayMap a P = 0 ↔ eval a (map (Int.castRingHom K) P) = 0
  rw [ray_homogeneous_value a P hP]
  constructor
  · intro hh
    have hz := (mul_eq_zero.mp hh).resolve_right (pow_ne_zero d (X_ne_zero ()))
    exact C_injective Unit K (hz.trans (map_zero C).symm)
  · intro hz
    rw [hz, map_zero, zero_mul]

theorem map_vector_ne_zero {L : Type*} [Field L] (φ : K →+* L)
    (a : σ → K) (ha : a ≠ 0) : φ ∘ a ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  intro h
  apply hi
  exact φ.injective ((congr_fun h i).trans (map_zero φ).symm)

theorem point_map {L : Type*} [Field L] (φ : K →+* L)
    (a : σ → K) (ha : a ≠ 0) :
    point (φ ∘ a) (map_vector_ne_zero φ a ha) = point a ha := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n P hP
  rw [homogeneous_mem_iff _ _ _ hP, homogeneous_mem_iff _ _ _ hP,
    ← integer_evaluation_map, map_eq_zero_iff φ φ.injective]

theorem scaled_vector_ne_zero (c : K) (hc : c ≠ 0) (a : σ → K) (ha : a ≠ 0) :
    (fun i ↦ c * a i) ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  intro h
  exact mul_ne_zero hc hi (congr_fun h i)

theorem point_scale (c : K) (hc : c ≠ 0) (a : σ → K) (ha : a ≠ 0) :
    point (fun i ↦ c * a i) (scaled_vector_ne_zero c hc a ha) = point a ha := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n P hP
  rw [homogeneous_mem_iff _ _ _ hP, homogeneous_mem_iff _ _ _ hP]
  have he := WeightedHomogeneousEvaluation.aeval_homogeneous_scale
    (map (Int.castRingHom K) P) (hP.map _) c a
  simp only [aeval_eq_eval] at he
  rw [he, mul_eq_zero]
  exact or_iff_right (pow_ne_zero n hc)

end Field

end PaperP1.IntegerCoefficientProjectivePoint
