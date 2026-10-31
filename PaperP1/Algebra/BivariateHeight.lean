module

public import PaperP1.Algebra.BivariateDegrees
public import PaperP1.Algebra.IntegerPolynomialRootBound
public import PaperP1.Analysis.BivariateSpecialization

/-! # Integer bivariate height and the exact rectangular coefficient norm

Both variable degrees and the finite support are literal. In particular the
coefficient count is (d_X+1)(d_Y+1), with no extra degree or height loss.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateHeight

open Polynomial Finset BivariateDegrees BivariateSpecialization MahlerCoefficientBounds

def height (P : ℤ[X][X]) : ℕ := P.support.sup fun i ↦ integerPolynomialHeight (P.coeff i)

def complexPolynomial (p : ℤ[X]) : ℂ[X] := p.map (Int.castRingHom ℂ)

def complexBivariate (P : ℤ[X][X]) : ℂ[X][X] :=
  P.map (Polynomial.mapRingHom (Int.castRingHom ℂ))

theorem complexBivariate_coeff (P : ℤ[X][X]) (i : ℕ) :
    (complexBivariate P).coeff i = complexPolynomial (P.coeff i) :=
  coeff_map (Polynomial.mapRingHom (Int.castRingHom ℂ)) i

theorem complexBivariate_coeff_coeff (P : ℤ[X][X]) (i j : ℕ) :
    ((complexBivariate P).coeff i).coeff j = ((P.coeff i).coeff j : ℂ) := by
  rw [complexBivariate_coeff]
  exact coeff_map (Int.castRingHom ℂ) j

theorem complexBivariate_mul (P Q : ℤ[X][X]) :
    complexBivariate (P * Q) = complexBivariate P * complexBivariate Q :=
  Polynomial.map_mul _

theorem complexPolynomial_mul (p q : ℤ[X]) :
    complexPolynomial (p * q) = complexPolynomial p * complexPolynomial q := Polynomial.map_mul _

theorem complexPolynomial_natDegree_le (p : ℤ[X]) :
    (complexPolynomial p).natDegree ≤ p.natDegree := natDegree_map_le

theorem complexBivariate_natDegree_le (P : ℤ[X][X]) :
    (complexBivariate P).natDegree ≤ degreeY P := natDegree_map_le

theorem natDegree_complex_coeff_le (P : ℤ[X][X]) (i : ℕ) :
    ((complexBivariate P).coeff i).natDegree ≤ degreeX P := by
  rw [complexBivariate_coeff]
  exact (complexPolynomial_natDegree_le _).trans (natDegree_coeff_le_degreeX P i)

theorem coefficient_natAbs_le_height (P : ℤ[X][X]) (i j : ℕ) :
    ((P.coeff i).coeff j).natAbs ≤ height P := by
  by_cases hi : i ∈ P.support
  · exact (coeff_natAbs_le_integerPolynomialHeight _ j).trans
      (le_sup (f := fun k ↦ integerPolynomialHeight (P.coeff k)) hi)
  · rw [notMem_support_iff.mp hi]
    simp

theorem norm_complex_coeff (P : ℤ[X][X]) (i j : ℕ) :
    ‖((complexBivariate P).coeff i).coeff j‖ = (((P.coeff i).coeff j).natAbs : ℝ) := by
  rw [complexBivariate_coeff_coeff, Complex.norm_intCast, ← Int.cast_abs]
  simpa only [Int.cast_natCast] using congrArg (fun n : ℤ ↦ (n : ℝ))
    (Int.abs_eq_natAbs ((P.coeff i).coeff j))

theorem norm_complex_coeff_le_height (P : ℤ[X][X]) (i j : ℕ) :
    ‖((complexBivariate P).coeff i).coeff j‖ ≤ (height P : ℝ) := by
  rw [norm_complex_coeff]
  exact_mod_cast coefficient_natAbs_le_height P i j

theorem height_le_of_complex_coeff_bound (P : ℤ[X][X]) (H : ℝ) (hH : 0 ≤ H)
    (hcoeff : ∀ i j, ‖((complexBivariate P).coeff i).coeff j‖ ≤ H) : (height P : ℝ) ≤ H := by
  have hnat : height P ≤ ⌊H⌋₊ := by
    unfold height integerPolynomialHeight
    apply Finset.sup_le
    intro i _
    apply Finset.sup_le
    intro j _
    apply Nat.le_floor
    rw [← norm_complex_coeff]
    exact hcoeff i j
  exact (by exact_mod_cast hnat : (height P : ℝ) ≤ (⌊H⌋₊ : ℝ)).trans (Nat.floor_le hH)

theorem support_complex_outer_le (P : ℤ[X][X]) :
    (complexBivariate P).support.card ≤ degreeY P + 1 :=
  (card_support_le_natDegree_add_one _).trans (Nat.add_le_add_right (complexBivariate_natDegree_le P) 1)

theorem support_complex_inner_le (P : ℤ[X][X]) (i : ℕ) :
    ((complexBivariate P).coeff i).support.card ≤ degreeX P + 1 :=
  (card_support_le_natDegree_add_one _).trans (Nat.add_le_add_right (natDegree_complex_coeff_le P i) 1)

theorem bivariate_energy_le_height (P : ℤ[X][X]) :
    bivariateCoefficientEnergy (complexBivariate P) ≤
      (((degreeX P + 1) * (degreeY P + 1) : ℕ) : ℝ) * (height P : ℝ) ^ 2 := by
  have hHsq : 0 ≤ (height P : ℝ) ^ 2 := sq_nonneg _
  calc
    _ ≤ ∑ _i ∈ (complexBivariate P).support, ((degreeX P + 1 : ℕ) : ℝ) * (height P : ℝ) ^ 2 := by
      apply sum_le_sum
      intro i _
      have he := coefficientEnergy_le_card_mul_sq ((complexBivariate P).coeff i) (height P)
        (norm_complex_coeff_le_height P i)
      have hc : (((complexBivariate P).coeff i).support.card : ℝ) ≤ ((degreeX P + 1 : ℕ) : ℝ) := by
        exact_mod_cast support_complex_inner_le P i
      exact he.trans (mul_le_mul_of_nonneg_right hc hHsq)
    _ = ((complexBivariate P).support.card : ℝ) *
        ((degreeX P + 1 : ℕ) : ℝ) * (height P : ℝ) ^ 2 := by
      simp only [sum_const, nsmul_eq_mul]
      ring
    _ ≤ ((degreeY P + 1 : ℕ) : ℝ) * ((degreeX P + 1 : ℕ) : ℝ) * (height P : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hHsq
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast support_complex_outer_le P
    _ = _ := by push_cast; ring

theorem bivariate_l2_le_height (P : ℤ[X][X]) :
    bivariateL2Norm (complexBivariate P) ≤
      Real.sqrt (((degreeX P + 1) * (degreeY P + 1) : ℕ) : ℝ) * (height P : ℝ) := by
  apply (sq_le_sq₀ (bivariateL2Norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))).mp
  rw [bivariateL2Norm_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact bivariate_energy_le_height P

end PaperP1.BivariateHeight
