module

public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.Rat
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

/-! # Nonconstant integer multivariate primes remain prime over the rationals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalMultivariatePrime

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem map_nonunit (F : MvPolynomial (Fin 2) ℤ) (hF : ∀ z : ℤ, F ≠ MvPolynomial.C z) :
    ¬ IsUnit (MvPolynomial.map (Int.castRingHom ℚ) F) := by
  intro hu
  obtain ⟨q, _, hq⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  have hc : (Int.castRingHom ℚ) (F.coeff 0) = q := by
    simpa [MvPolynomial.coeff_map] using congrArg (fun P : MvPolynomial (Fin 2) ℚ ↦ P.coeff 0) hq
  have hm : MvPolynomial.map (Int.castRingHom ℚ) F =
      MvPolynomial.map (Int.castRingHom ℚ) (MvPolynomial.C (F.coeff 0)) := by
    rw [MvPolynomial.map_C, hc]
    exact hq
  exact hF _ (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective hm)

theorem prime_map (F : MvPolynomial (Fin 2) ℤ) (hp : Prime F)
    (hF : ∀ z : ℤ, F ≠ MvPolynomial.C z) :
    Prime (MvPolynomial.map (Int.castRingHom ℚ) F) := by
  let f := IsLocalization.toLocalizationMap
    ((nonZeroDivisors ℤ).map (MvPolynomial.C (σ := Fin 2))) (MvPolynomial (Fin 2) ℚ)
  have hf : ∀ P : MvPolynomial (Fin 2) ℤ, f P = MvPolynomial.map (Int.castRingHom ℚ) P := by
    intro P
    simp only [f, IsLocalization.toLocalizationMap_apply, MvPolynomial.algebraMap_def]
    rfl
  have hzero : f F ≠ 0 := by
    rw [hf]
    intro hz
    apply hp.ne_zero
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    simpa only [map_zero] using hz
  have hunit : ¬ IsUnit (f F) := by rw [hf]; exact map_nonunit F hF
  simpa only [hf] using f.map_prime hp hzero hunit

end PaperP1.RationalMultivariatePrime
