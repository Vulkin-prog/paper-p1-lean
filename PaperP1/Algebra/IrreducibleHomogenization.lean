module

public import PaperP1.Algebra.HomogeneousFactorDegrees
public import PaperP1.Diophantine.HomogeneousCharts
public import Mathlib.Algebra.Polynomial.Degree.Units

/-! # Full-degree homogenization preserves irreducibility over a domain -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IrreducibleHomogenization

open Polynomial PaperP1.HomogeneousCharts

variable {R : Type*} [CommRing R] [IsDomain R]

theorem shape_of_chart_unit (F : MvPolynomial (Fin 2) R) (d : ℕ)
    (hF : F.IsHomogeneous d) (hu : IsUnit (chart F)) :
    ∃ c : R, IsUnit c ∧ F = MvPolynomial.C c * MvPolynomial.X 1 ^ d := by
  obtain ⟨c, hc, he⟩ := Polynomial.isUnit_iff.mp hu
  refine ⟨c, hc, ?_⟩
  rw [← chart_homogenize F hF, ← he, Polynomial.homogenize_C]

theorem homogeneous_unit_of_chart_unit (F : MvPolynomial (Fin 2) R) (d : ℕ)
    (hF : F.IsHomogeneous d) (hu : IsUnit (chart F))
    (hX : ¬MvPolynomial.X (1 : Fin 2) ∣ F) : IsUnit F := by
  obtain ⟨c, hc, he⟩ := shape_of_chart_unit F d hF hu
  have hd : d = 0 := by
    by_contra hd
    apply hX
    rw [he]
    exact dvd_mul_of_dvd_right (dvd_pow_self _ hd) _
  rw [he, hd, pow_zero, mul_one]
  exact hc.map (MvPolynomial.C : R →+* MvPolynomial (Fin 2) R)

omit [IsDomain R] in
theorem not_X_one_dvd_homogenize (P : R[X]) (hP : P ≠ 0) :
    ¬MvPolynomial.X (1 : Fin 2) ∣ P.homogenize P.natDegree := by
  classical
  rintro ⟨Q, hQ⟩
  have hc : (P.homogenize P.natDegree).coeff (Finsupp.single (0 : Fin 2) P.natDegree) =
      P.leadingCoeff := by
    simp [Polynomial.coeff_homogenize]
  have hz : (P.homogenize P.natDegree).coeff (Finsupp.single (0 : Fin 2) P.natDegree) = 0 := by
    rw [hQ, MvPolynomial.coeff_X_mul']
    simp
  exact (Polynomial.leadingCoeff_ne_zero.mpr hP) (hc.symm.trans hz)

theorem homogenize_irreducible (P : R[X]) (hP : Irreducible P) :
    Irreducible (P.homogenize P.natDegree) := by
  have hH : P.homogenize P.natDegree ≠ 0 :=
    (Polynomial.homogenize_eq_zero_iff le_rfl).not.mpr hP.ne_zero
  have hX := not_X_one_dvd_homogenize P hP.ne_zero
  have hchart : chart (P.homogenize P.natDegree) = P :=
    Polynomial.aeval_homogenize_X_one P le_rfl
  refine ⟨?_, ?_⟩
  · intro hu
    have hh : IsUnit (chart (P.homogenize P.natDegree)) :=
      hu.map (MvPolynomial.aeval ![Polynomial.X, 1]).toRingHom
    exact hP.1 (hchart ▸ hh)
  · intro A B hAB
    have hABne : A * B ≠ 0 := by rw [← hAB]; exact hH
    have hhom : (A * B).IsHomogeneous P.natDegree := by
      rw [← hAB]
      exact Polynomial.isHomogeneous_homogenize P
    obtain ⟨hA, hB⟩ := PaperP1.HomogeneousFactorDegrees.homogeneous_factors A B hABne P.natDegree hhom
    have heq : P = chart A * chart B := by
      have he := congrArg (MvPolynomial.aeval (R := R) ![(Polynomial.X : R[X]), 1]) hAB
      simpa only [chart, map_mul, Polynomial.aeval_homogenize_X_one P le_rfl] using he
    rcases hP.2 heq with hu | hu
    · left
      apply homogeneous_unit_of_chart_unit A A.totalDegree hA hu
      intro hdiv
      apply hX
      rw [hAB]
      exact dvd_mul_of_dvd_left hdiv B
    · right
      apply homogeneous_unit_of_chart_unit B B.totalDegree hB hu
      intro hdiv
      apply hX
      rw [hAB]
      exact dvd_mul_of_dvd_right hdiv A

end PaperP1.IrreducibleHomogenization
