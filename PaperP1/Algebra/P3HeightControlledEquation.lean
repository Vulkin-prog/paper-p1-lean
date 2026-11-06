module

public import PaperP1.Algebra.P3HomogeneousIntegerInterpolation
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # An actual bounded integer model or a distinct auxiliary equation on the original points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3HeightControlledEquation

open MvPolynomial P3HomogeneousCoefficientFamily

theorem scalar_of_dvd {F σ : Type*} [Field F] (d : ℕ) (P Q : MvPolynomial σ F)
    (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous d) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)
    (hdiv : P ∣ Q) : ∃ c : F, c ≠ 0 ∧ Q = C c * P := by
  obtain ⟨A, hA⟩ := hdiv
  have hA0 : A ≠ 0 := by
    intro hz
    apply hQ0
    rw [hA, hz, mul_zero]
  have he := MvPolynomial.totalDegree_mul_of_isDomain hP0 hA0
  rw [← hA, hP.totalDegree hP0, hQ.totalDegree hQ0] at he
  have hdA : A.totalDegree = 0 := by omega
  have hAc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdA
  refine ⟨A.coeff 0, ?_, ?_⟩
  · intro hz
    apply hA0
    rw [hAc, hz, map_zero]
  · calc
      Q = P * A := hA
      _ = P * C (A.coeff 0) := congrArg (fun B ↦ P * B) hAc
      _ = C (A.coeff 0) * P := mul_comm _ _

theorem integer_evaluation {σ : Type*} (Q : MvPolynomial σ ℤ) (v : σ → ℤ) :
    eval (fun i ↦ (v i : ℚ)) (map (Int.castRingHom ℚ) Q) = (eval v Q : ℚ) := by
  rw [eval_map]
  exact (eval₂_comp (Int.castRingHom ℚ) v Q).symm

theorem exists_model_or_auxiliary (d H : ℕ) (hH : 1 ≤ H) (U : Finset (Fin 4 → ℤ))
    (hheight : ∀ v ∈ U, ∀ i, |v i| ≤ (H : ℤ))
    (P : MvPolynomial (Fin 4) ℚ) (hP : P.IsHomogeneous d) (hP0 : P ≠ 0)
    (hroots : ∀ v ∈ U, eval (fun k ↦ (v k : ℚ)) P = 0) :
    ∃ Q : MvPolynomial (Fin 4) ℤ, Q.IsHomogeneous d ∧ Q ≠ 0 ∧
      (∀ m, |Q.coeff m| ≤ (((3 * Fintype.card (Index d) * H ^ d) ^
        (Fintype.card (Index d) - 1) : ℕ) : ℤ)) ∧ (∀ v ∈ U, eval v Q = 0) ∧
      (¬ P ∣ map (Int.castRingHom ℚ) Q ∨
        ∃ c : ℚ, c ≠ 0 ∧ map (Int.castRingHom ℚ) Q = C c * P) := by
  classical
  obtain ⟨Q, hQ, hQ0, hbound, hzero⟩ :=
    P3HomogeneousIntegerInterpolation.exists_bounded_equation d H hH U hheight P hP hP0 hroots
  refine ⟨Q, hQ, hQ0, hbound, hzero, ?_⟩
  by_cases hdiv : P ∣ map (Int.castRingHom ℚ) Q
  · apply Or.inr
    have hmap0 : map (Int.castRingHom ℚ) Q ≠ 0 := by
      intro hz
      apply hQ0
      exact map_injective (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
        (hz.trans (map_zero _).symm)
    exact scalar_of_dvd d P (map (Int.castRingHom ℚ) Q) hP (hQ.map _) hP0 hmap0 hdiv
  · exact Or.inl hdiv

end PaperP1.P3HeightControlledEquation
