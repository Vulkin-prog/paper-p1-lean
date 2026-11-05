module

public import PaperP1.Diophantine.HomogeneousCharts

/-! # Coefficient maps commute with the homogeneous chart, including the axis evaluation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousChartSpecialization

open Polynomial Finset PaperP1.HomogeneousCharts

theorem chart_map {R S : Type*} [CommRing R] [CommRing S]
    (F : MvPolynomial (Fin 2) R) (d : ℕ) (hF : F.IsHomogeneous d) (f : R →+* S) :
    chart (MvPolynomial.map f F) = (chart F).map f := by
  have hd : ((chart F).map f).natDegree ≤ d :=
    Polynomial.natDegree_map_le.trans (chart_degree F hF)
  conv_lhs => rw [← chart_homogenize F hF, ← Polynomial.homogenize_map]
  exact Polynomial.aeval_homogenize_X_one _ hd

theorem eval_homogenize_axis {R : Type*} [CommRing R] (P : R[X]) (d : ℕ) (t : R) :
    MvPolynomial.eval ![t, 0] (P.homogenize d) = P.coeff d * t ^ d := by
  classical
  rw [Polynomial.homogenize, map_sum]
  simp only [MvPolynomial.eval_monomial]
  rw [Finset.sum_eq_single (d, 0)]
  · simp
  · intro kl hkl hne
    have hs := Finset.mem_antidiagonal.mp hkl
    have hz : kl.2 ≠ 0 := by
      intro hzero
      apply hne
      exact Prod.ext (by omega) hzero
    simp [zero_pow hz]
  · intro hnot
    exact False.elim (hnot (Finset.mem_antidiagonal.mpr (by omega)))

end PaperP1.HomogeneousChartSpecialization
