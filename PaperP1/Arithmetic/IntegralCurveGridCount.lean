module

public import PaperP1.Arithmetic.FiniteNormalizationIntegerCount
public import PaperP1.Geometry.OriginalFieldCurveNoetherNormalization

/-! # Every actual integral curve over its original characteristic-zero field has the controlled projected-height count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegralCurveGridCount

universe u

open MvPolynomial IntegerCurveProjectionCoordinates QuadraticDegreeUniformFieldCount
attribute [local instance] MvPolynomial.gradedAlgebra

theorem population_bound {F : Type u} [Field F] [CharZero F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) F)) (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) F))
    (hprime : I.IsPrime) (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    (z : Fin n) (H : ℕ) (hH : 1 ≤ H) (S : Finset (Fin n → ℤ))
    (hnormal : ∀ w ∈ S, w z = 1)
    (hcurve : ∀ w ∈ S, ∀ P ∈ I, eval (fun i ↦ (w i : F)) P = 0)
    (hheight : ∀ w ∈ S, ∀ i, (w i).natAbs ≤ H) :
    (S.card : ℝ) ≤ (QuadraticAllDegreePlaneCount.constant.{u} + 1) *
      profile d (n * (((n - 1) * d ^ 2 + 1) ^ (n - 1)) * H) := by
  classical
  by_cases hz : X z ∈ I
  · have hzero : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro w hw
      have hh := hcurve w hw (X z) hz
      rw [eval_X, hnormal w hw, Int.cast_one] at hh
      exact one_ne_zero hh
    rw [hzero, Finset.card_empty, Nat.cast_zero]
    have hC := QuadraticAllDegreePlaneCount.constant_pos.{u}
    unfold profile
    positivity
  let : I.IsPrime := hprime
  obtain ⟨u₀, hu, hfinite, hinj, hrank⟩ := OriginalFieldCurveNoetherNormalization.exists_normalization
    n I hI hprime d hd b₀ hp z hz
  let A := MvPolynomial (Fin n) F ⧸ I
  let g := parameters I z u₀
  let : Algebra (MvPolynomial (Fin 2) F) A := (aeval (R := F) g).toRingHom.toAlgebra
  let : IsScalarTower F (MvPolynomial (Fin 2) F) A :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ ((aeval (R := F) g).commutes r).symm)
  have hu' : ∀ i, u₀ i ≤ ((n - 1) * d ^ 2 + 1) ^ (n - 1) := by
    intro i
    have hd2 : d ≤ d ^ 2 := le_self_pow₀ (by omega) (by decide : 2 ≠ 0)
    have hh : (n - 1) * d + 1 ≤ (n - 1) * d ^ 2 + 1 := by gcongr
    exact (hu i).trans (Nat.pow_le_pow_left hh (n - 1))
  obtain ⟨_v, _hv, hcount⟩ := FiniteNormalizationIntegerCount.exists_primitive_count I hI d hd b₀ hp
    z u₀ rfl hfinite hinj hrank hu'
  exact hcount H hH S hnormal hcurve hheight

end PaperP1.IntegralCurveGridCount
