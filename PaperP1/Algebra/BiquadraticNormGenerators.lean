module

public import PaperP1.Algebra.BiquadraticNormModel

/-! # The two actual quadratic generators and the source third radical in the norm model -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticNormGenerators

open PaperP1.BiquadraticNormModel

def base {R : Type*} [CommRing R] (f g : R) : R →+* Second R f g :=
  (algebraMap (First R f) (Second R f g)).comp (algebraMap R (First R f))

theorem base_eq {R : Type*} [CommRing R] (f g : R) : base f g = algebraMap R (Second R f g) := rfl

def firstRoot {R : Type*} [CommRing R] (f g : R) : Second R f g :=
  algebraMap (First R f) (Second R f g) QuadraticAlgebra.omega

def secondRoot {R : Type*} [CommRing R] (f g : R) : Second R f g := QuadraticAlgebra.omega

def thirdRoot {K : Type*} [Field K] (f g G : K) : Second K f g :=
  base f g G⁻¹ * firstRoot f g * secondRoot f g

theorem first_square {R : Type*} [CommRing R] (f g : R) : (firstRoot f g) ^ 2 = base f g f := by
  unfold firstRoot base
  rw [← map_pow, pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero]
  rfl

theorem second_square {R : Type*} [CommRing R] (f g : R) : (secondRoot f g) ^ 2 = base f g g := by
  unfold secondRoot base
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero]
  rfl

theorem overlap_relation {K : Type*} [Field K] (f g G : K) (hG : G ≠ 0) :
    base f g G * thirdRoot f g G = firstRoot f g * secondRoot f g := by
  unfold thirdRoot
  rw [← mul_assoc, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hG, map_one, one_mul]

theorem third_square {K : Type*} [Field K] (f g G f₃ : K) (hG : G ≠ 0)
    (h₃ : f₃ * G ^ 2 = f * g) : (thirdRoot f g G) ^ 2 = base f g f₃ := by
  have he : f₃ = f * g / G ^ 2 := (eq_div_iff (pow_ne_zero 2 hG)).mpr h₃
  calc
    _ = base f g G⁻¹ ^ 2 * (firstRoot f g ^ 2 * secondRoot f g ^ 2) := by unfold thirdRoot; ring
    _ = base f g ((G⁻¹) ^ 2 * (f * g)) := by rw [first_square, second_square, ← map_pow, ← map_mul, ← map_mul]
    _ = _ := by
      apply congrArg (base f g)
      rw [he]
      field_simp

theorem auxiliary_expansion {K : Type*} [Field K] (f g G a b c d : K) :
    auxiliary f g a b c (d / G) = base f g a + base f g b * firstRoot f g +
      base f g c * secondRoot f g + base f g d * thirdRoot f g G := by
  ext <;> simp [auxiliary, base, firstRoot, secondRoot, thirdRoot, QuadraticAlgebra.omega,
    RingHom.comp_apply, div_eq_mul_inv]

theorem generators_top {K : Type*} [Field K] (f g : K) :
    Algebra.adjoin K ({firstRoot f g, secondRoot f g} : Set (Second K f g)) = ⊤ := by
  let A := Algebra.adjoin K ({firstRoot f g, secondRoot f g} : Set (Second K f g))
  have h₁ : firstRoot f g ∈ A := Algebra.subset_adjoin (by simp)
  have h₂ : secondRoot f g ∈ A := Algebra.subset_adjoin (by simp)
  have hb : ∀ a : K, base f g a ∈ A := by
    intro a
    rw [base_eq]
    exact A.algebraMap_mem a
  apply Algebra.eq_top_iff.mpr
  intro z
  change auxiliary f g z.re.re z.re.im z.im.re z.im.im ∈ A
  have hexp := auxiliary_expansion f g 1 z.re.re z.re.im z.im.re z.im.im
  simp only [div_one, thirdRoot, inv_one, map_one, one_mul] at hexp
  rw [hexp]
  exact A.add_mem (A.add_mem (A.add_mem (hb _) (A.mul_mem (hb _) h₁)) (A.mul_mem (hb _) h₂))
    (A.mul_mem (hb _) (A.mul_mem h₁ h₂))

end PaperP1.BiquadraticNormGenerators
