module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Ring.Divisibility.Basic

/-! # A monic principal generator of an actual homogeneous ideal is homogeneous of its monic degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousMonicGenerator

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cons_degree {n : ℕ} (i : ℕ) (d : Fin n →₀ ℕ) : (d.cons i).degree = i + d.degree := by
  simp only [Finsupp.degree_eq_sum, Fin.sum_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ]

theorem component_coefficient {F : Type*} [CommRing F] {n : ℕ}
    (q : MvPolynomial (Fin (n + 1)) F) (i j : ℕ) :
    (finSuccEquiv F n (homogeneousComponent (i + j) q)).coeff i =
      homogeneousComponent j ((finSuccEquiv F n q).coeff i) := by
  apply MvPolynomial.ext
  intro d
  simp only [finSuccEquiv_coeff_coeff, coeff_homogeneousComponent, cons_degree, Nat.add_left_cancel_iff]

theorem homogeneous {F : Type*} [Field F] {n : ℕ} (q : MvPolynomial (Fin (n + 1)) F)
    (hI : (Ideal.span {q}).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) F))
    (hmonic : (finSuccEquiv F n q).Monic) : q.IsHomogeneous (finSuccEquiv F n q).natDegree := by
  let e := (finSuccEquiv F n q).natDegree
  let m := homogeneousComponent e q
  have hmhom : m.IsHomogeneous e := homogeneousComponent_isHomogeneous e q
  have hcoeff : (finSuccEquiv F n q).coeff e = 1 := hmonic.coeff_natDegree
  have hmcoeff : (finSuccEquiv F n m).coeff e = 1 := by
    simpa [m, hcoeff, homogeneousComponent_zero] using component_coefficient q e 0
  have hm0 : m ≠ 0 := by
    intro hz
    have hh := hmcoeff
    rw [hz, map_zero, Polynomial.coeff_zero] at hh
    exact zero_ne_one hh
  have hmle : (finSuccEquiv F n m).natDegree ≤ e := by
    rw [natDegree_finSuccEquiv]
    exact (degreeOf_le_totalDegree m 0).trans (le_of_eq (hmhom.totalDegree hm0))
  have hmdegree : (finSuccEquiv F n m).natDegree = e :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hmle (by rw [hmcoeff]; exact one_ne_zero)
  have hmmonic : (finSuccEquiv F n m).Monic := by
    change (finSuccEquiv F n m).leadingCoeff = 1
    rw [Polynomial.leadingCoeff, hmdegree, hmcoeff]
  have hdiv : q ∣ m := by
    apply Ideal.mem_span_singleton.mp
    exact ((mem_iff_homogeneousComponent_mem hI q).mp (Ideal.mem_span_singleton_self q)) e
  have heq := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic hmmonic
    (map_dvd (finSuccEquiv F n).toRingHom hdiv) hmle
  rwa [(finSuccEquiv F n).injective heq] at hmhom

end PaperP1.HomogeneousMonicGenerator
