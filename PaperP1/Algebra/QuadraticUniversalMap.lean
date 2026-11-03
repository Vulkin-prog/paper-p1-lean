module

public import PaperP1.Algebra.BiquadraticNormModel

/-! # The actual universal ring map out of one quadratic radical algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticUniversalMap

open QuadraticAlgebra

def liftRing {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) (u : S) (hu : u ^ 2 = φ f) : QuadraticAlgebra R f 0 →+* S where
  toFun z := φ z.re + φ z.im * u
  map_zero' := by simp only [re_zero, im_zero, map_zero, zero_mul, add_zero]
  map_one' := by simp only [re_one, im_one, map_one, map_zero, zero_mul, add_zero]
  map_add' z w := by simp only [re_add, im_add, map_add]; ring
  map_mul' z w := by
    simp only [re_mul, im_mul, zero_mul, add_zero, map_add, map_mul]
    linear_combination -(φ z.im * φ w.im) * hu

theorem liftRing_apply {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) (u : S) (hu : u ^ 2 = φ f) (z : QuadraticAlgebra R f 0) :
    liftRing φ f u hu z = φ z.re + φ z.im * u := rfl

theorem liftRing_base {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) (u : S) (hu : u ^ 2 = φ f) (r : R) :
    liftRing φ f u hu (algebraMap R (QuadraticAlgebra R f 0) r) = φ r := by
  rw [liftRing_apply, algebraMap_re, algebraMap_im, map_zero, zero_mul, add_zero]

theorem liftRing_omega {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) (u : S) (hu : u ^ 2 = φ f) :
    liftRing φ f u hu omega = u := by
  rw [liftRing_apply, re_omega, im_omega, map_zero, map_one, one_mul, zero_add]

theorem hom_ext {R S : Type*} [CommRing R] [CommRing S] (f : R)
    (φ ψ : QuadraticAlgebra R f 0 →+* S)
    (hbase : ∀ r, φ (algebraMap R (QuadraticAlgebra R f 0) r) = ψ (algebraMap R (QuadraticAlgebra R f 0) r))
    (hroot : φ omega = ψ omega) : φ = ψ := by
  apply RingHom.ext
  intro z
  have hrep : algebraMap R (QuadraticAlgebra R f 0) z.re +
      algebraMap R (QuadraticAlgebra R f 0) z.im * omega = z := by
    simpa only [Algebra.smul_def, mul_one] using re_smul_add_im_smul z
  rw [← hrep]
  simp only [map_add, map_mul, hbase, hroot]

theorem liftRing_unique {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R) (u : S) (hu : u ^ 2 = φ f) (ψ : QuadraticAlgebra R f 0 →+* S)
    (hbase : ∀ r, ψ (algebraMap R (QuadraticAlgebra R f 0) r) = φ r) (hroot : ψ omega = u) :
    ψ = liftRing φ f u hu := hom_ext f ψ _
      (fun r ↦ (hbase r).trans (liftRing_base φ f u hu r).symm)
      (hroot.trans (liftRing_omega φ f u hu).symm)

end PaperP1.QuadraticUniversalMap
