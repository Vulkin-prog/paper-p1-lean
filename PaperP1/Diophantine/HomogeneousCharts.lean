module

public import PaperP1.Diophantine.ProjectiveResultants

/-! # Exact coefficient and degree transport for homogeneous binary forms -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousCharts

open Polynomial

variable {R : Type*} [CommRing R]

def chart (F : MvPolynomial (Fin 2) R) : R[X] :=
  MvPolynomial.aeval ![Polynomial.X, 1] F

theorem chart_degree (F : MvPolynomial (Fin 2) R) {d : ℕ} (hF : F.IsHomogeneous d) :
    (chart F).natDegree ≤ d := by
  classical
  unfold chart
  rw [F.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have hdeg : m 0 + m 1 = d := by
    have h := hF (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using h
  rw [MvPolynomial.aeval_monomial]
  simpa [Finsupp.prod_fintype] using
    (Polynomial.natDegree_C_mul_X_pow_le (F.coeff m) (m 0)).trans (show m 0 ≤ d by omega)

theorem chart_homogenize (F : MvPolynomial (Fin 2) R) {d : ℕ} (hF : F.IsHomogeneous d) :
    (chart F).homogenize d = F :=
  Polynomial.homogenize_eq_of_isHomogeneous hF rfl

theorem chart_coeff (F : MvPolynomial (Fin 2) R) {d : ℕ} (hF : F.IsHomogeneous d)
    (j : ℕ) (hj : j ≤ d) :
    (chart F).coeff j = F.coeff (fun₀ | 0 => j | 1 => d - j) := by
  have h := congrArg (fun P : MvPolynomial (Fin 2) R ↦
    P.coeff (fun₀ | 0 => j | 1 => d - j)) (chart_homogenize F hF)
  simpa [Polynomial.coeff_homogenize, Nat.add_sub_of_le hj] using h

theorem chart_coefficient_bound (F : MvPolynomial (Fin 2) ℤ) {d : ℕ}
    (hF : F.IsHomogeneous d) (B : ℝ) (hB : 0 ≤ B)
    (hcoeff : ∀ m, ((F.coeff m).natAbs : ℝ) ≤ B) :
    ∀ j, (((chart F).coeff j).natAbs : ℝ) ≤ B := by
  intro j
  by_cases hj : j ≤ d
  · rw [chart_coeff F hF j hj]
    exact hcoeff _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((chart_degree F hF).trans_lt (by omega))]
    simpa only [Int.natAbs_zero, Nat.cast_zero] using hB

theorem integer_resultant_ne_zero (F G : MvPolynomial (Fin 2) ℤ) (d : ℕ) (hd : 0 < d)
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (hcop : IsRelPrime (MvPolynomial.map (Int.castRingHom ℚ) F)
      (MvPolynomial.map (Int.castRingHom ℚ) G)) :
    (chart F).resultant (chart G) d d ≠ 0 := by
  let φ := Int.castRingHom ℚ
  have hf := chart_degree F hF
  have hg := chart_degree G hG
  have hdf := Polynomial.natDegree_map_eq_of_injective (f := φ) (by exact Int.cast_injective) (chart F)
  have hdg := Polynomial.natDegree_map_eq_of_injective (f := φ) (by exact Int.cast_injective) (chart G)
  have hhom : IsRelPrime (((chart F).map φ).homogenize d) (((chart G).map φ).homogenize d) := by
    simpa only [Polynomial.homogenize_map, chart_homogenize F hF, chart_homogenize G hG] using hcop
  have hres := PaperP1.ProjectiveResultants.resultant_ne_zero_of_homogeneous_relprime
    ((chart F).map φ) ((chart G).map φ) d hd
    (by simpa only [hdf] using hf) (by simpa only [hdg] using hg) hhom
  intro hz
  rw [Polynomial.resultant_map_map, hz, map_zero] at hres
  exact hres rfl

theorem integer_resultant_ne_zero_of_irreducible
    (F G : MvPolynomial (Fin 2) ℤ) (d : ℕ) (hd : 0 < d)
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (hirr : Irreducible
      (MvPolynomial.C (MvPolynomial.map (Int.castRingHom ℚ) F) * MvPolynomial.X (0 : Fin 2) +
       MvPolynomial.C (MvPolynomial.map (Int.castRingHom ℚ) G) * MvPolynomial.X 1)) :
    (chart F).resultant (chart G) d d ≠ 0 := by
  apply integer_resultant_ne_zero F G d hd hF hG
  exact PaperP1.ProjectiveResultants.coefficients_relprime_of_irreducible _ _ hirr

end PaperP1.HomogeneousCharts
