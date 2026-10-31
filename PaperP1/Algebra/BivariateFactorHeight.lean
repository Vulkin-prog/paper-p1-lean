module

public import PaperP1.Algebra.BivariateHeight

/-! # Exact bivariate factor-height bound (companion T9.4)

Only univariate Mahler inequalities and Parseval are needed. The fixed top
outer coefficient of the integral quotient has Mahler measure at least one.
The proof therefore covers every integral factorization of a nonzero product;
primitivity of the selected factor is unnecessary.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateFactorHeight

open Polynomial BivariateDegrees BivariateHeight BivariateSpecialization MahlerCoefficientBounds

/-- The elementary integral leading-coefficient argument, also used in Mathlib's
`Polynomial.one_le_mahlerMeasure_of_ne_zero`; no cyclotomic theory is needed. -/
theorem one_le_mahler_complexPolynomial (p : ℤ[X]) (hp : p ≠ 0) :
    1 ≤ (complexPolynomial p).mahlerMeasure := by
  apply le_trans _ (complexPolynomial p).leadingCoeff_le_mahlerMeasure
  change 1 ≤ ‖(p.map (Int.castRingHom ℂ)).leadingCoeff‖
  rw [leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int]
  change 1 ≤ ‖(p.leadingCoeff : ℂ)‖
  rw [Complex.norm_intCast]
  norm_cast
  exact Int.one_le_abs (leadingCoeff_ne_zero.mpr hp)

theorem mahler_outer_coefficient_le (Q R : ℤ[X][X]) (hR : R ≠ 0) (i : ℕ) :
    ((complexBivariate Q).coeff i).mahlerMeasure ≤
      (2 : ℝ) ^ degreeY Q * bivariateL2Norm (complexBivariate (Q * R)) := by
  have htop : R.coeff R.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hR
  have hM : 1 ≤ ((complexBivariate R).coeff R.natDegree).mahlerMeasure := by
    rw [complexBivariate_coeff]
    exact one_le_mahler_complexPolynomial _ htop
  calc
    _ ≤ ((complexBivariate Q).coeff i).mahlerMeasure *
        ((complexBivariate R).coeff R.natDegree).mahlerMeasure := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hM
        ((complexBivariate Q).coeff i).mahlerMeasure_nonneg
    _ = (((complexBivariate Q).coeff i) *
        ((complexBivariate R).coeff R.natDegree)).mahlerMeasure := (mahlerMeasure_mul _ _).symm
    _ ≤ l2CoefficientNorm (((complexBivariate Q).coeff i) *
        ((complexBivariate R).coeff R.natDegree)) := mahler_le_l2 _
    _ ≤ (2 : ℝ) ^ degreeY Q *
        bivariateL2Norm (complexBivariate Q * complexBivariate R) :=
      factor_outer_coefficient_l2_bound _ _ (degreeY Q) (degreeY R) i
        (complexBivariate_natDegree_le Q) (complexBivariate_natDegree_le R)
    _ = _ := by rw [complexBivariate_mul]

theorem factor_coefficient_le_own_degrees (Q R : ℤ[X][X]) (hR : R ≠ 0) (i j : ℕ) :
    ‖((complexBivariate Q).coeff i).coeff j‖ ≤
      (2 : ℝ) ^ (degreeX Q + degreeY Q) * bivariateL2Norm (complexBivariate (Q * R)) := by
  calc
    _ ≤ ((degreeX Q).choose j : ℝ) * ((complexBivariate Q).coeff i).mahlerMeasure :=
      norm_coeff_le_choose_mul_mahler_of_degree_bound _ _ _ (natDegree_complex_coeff_le Q i)
    _ ≤ (2 : ℝ) ^ degreeX Q * ((complexBivariate Q).coeff i).mahlerMeasure := by
      apply mul_le_mul_of_nonneg_right _ ((complexBivariate Q).coeff i).mahlerMeasure_nonneg
      exact_mod_cast Nat.choose_le_two_pow (degreeX Q) j
    _ ≤ (2 : ℝ) ^ degreeX Q *
        ((2 : ℝ) ^ degreeY Q * bivariateL2Norm (complexBivariate (Q * R))) :=
      mul_le_mul_of_nonneg_left (mahler_outer_coefficient_le Q R hR i) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem factor_height_le_l2 (Q R : ℤ[X][X]) (hQR : Q * R ≠ 0) :
    (height Q : ℝ) ≤ (2 : ℝ) ^ (degreeX (Q * R) + degreeY (Q * R)) *
      bivariateL2Norm (complexBivariate (Q * R)) := by
  apply height_le_of_complex_coeff_bound _ _
    (mul_nonneg (by positivity) (bivariateL2Norm_nonneg _))
  intro i j
  apply (factor_coefficient_le_own_degrees Q R (right_ne_zero_of_mul hQR) i j).trans
  apply mul_le_mul_of_nonneg_right _ (bivariateL2Norm_nonneg _)
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  exact Nat.add_le_add (factor_degreeX_le Q R hQR) (factor_natDegree_le Q R hQR)

/-- The exact T9.4 chain for every integer factor, without a primitive hypothesis. -/
theorem companion_T9_4 (Q R : ℤ[X][X]) (hQR : Q * R ≠ 0) :
    (height Q : ℝ) ≤ (2 : ℝ) ^ (degreeX (Q * R) + degreeY (Q * R)) *
        bivariateL2Norm (complexBivariate (Q * R)) ∧
      (2 : ℝ) ^ (degreeX (Q * R) + degreeY (Q * R)) *
        bivariateL2Norm (complexBivariate (Q * R)) ≤
      (2 : ℝ) ^ (degreeX (Q * R) + degreeY (Q * R)) *
        Real.sqrt (((degreeX (Q * R) + 1) * (degreeY (Q * R) + 1) : ℕ) : ℝ) *
        (height (Q * R) : ℝ) := by
  refine ⟨factor_height_le_l2 Q R hQR, ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (bivariate_l2_le_height (Q * R))
    (by positivity : 0 ≤ (2 : ℝ) ^ (degreeX (Q * R) + degreeY (Q * R)))

theorem quotient_height_le_l2 (Q R : ℤ[X][X]) (hQR : Q * R ≠ 0) :
    (height R : ℝ) ≤ (2 : ℝ) ^ (degreeX (Q * R) + degreeY (Q * R)) *
      bivariateL2Norm (complexBivariate (Q * R)) := by
  have hRQ : R * Q ≠ 0 := by simpa only [mul_comm] using hQR
  simpa only [mul_comm] using factor_height_le_l2 R Q hRQ

/-- Literal nonzero manuscript polynomial and its integer factorization;
both factors share the same exact norm and height constants. -/
theorem companion_T9_4_factor_and_quotient (P Q R : ℤ[X][X]) (hP : P ≠ 0)
    (hfactor : P = Q * R) :
    (height Q : ℝ) ≤ (2 : ℝ) ^ (degreeX P + degreeY P) *
        bivariateL2Norm (complexBivariate P) ∧
      (height R : ℝ) ≤ (2 : ℝ) ^ (degreeX P + degreeY P) *
        bivariateL2Norm (complexBivariate P) ∧
      (2 : ℝ) ^ (degreeX P + degreeY P) * bivariateL2Norm (complexBivariate P) ≤
        (2 : ℝ) ^ (degreeX P + degreeY P) *
          Real.sqrt (((degreeX P + 1) * (degreeY P + 1) : ℕ) : ℝ) * (height P : ℝ) := by
  subst P
  exact ⟨(companion_T9_4 Q R hP).1, quotient_height_le_l2 Q R hP,
    (companion_T9_4 Q R hP).2⟩

end PaperP1.BivariateFactorHeight
