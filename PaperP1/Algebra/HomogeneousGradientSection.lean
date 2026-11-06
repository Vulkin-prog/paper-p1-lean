module

public import PaperP1.Algebra.HomogeneousQuotientGrading
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic.Push
public import Lean.Elab.Tactic.Omega

/-! # A positive-degree homogeneous hypersurface has an actual nonzero homogeneous partial-derivative section in characteristic zero -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousGradientSection

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F σ : Type*} [Field F] [CharZero F] [Fintype σ]

theorem exists_nonzero_partial (d : ℕ) (hd : 0 < d) (q : MvPolynomial σ F)
    (hq : q.IsHomogeneous d) (hq0 : q ≠ 0) : ∃ i, pderiv i q ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hscale : d • q ≠ 0 := by
    rw [nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)) hq0
  apply hscale
  rw [← hq.sum_X_mul_pderiv]
  simp only [hn, mul_zero, Finset.sum_const_zero]

theorem exists_partial_not_mem (d : ℕ) (hd : 0 < d) (q : MvPolynomial σ F)
    (hq : q.IsHomogeneous d) (hq0 : q ≠ 0) :
    ∃ i, (pderiv i q).IsHomogeneous (d - 1) ∧ pderiv i q ≠ 0 ∧ pderiv i q ∉ Ideal.span {q} := by
  obtain ⟨i, hi⟩ := exists_nonzero_partial d hd q hq hq0
  refine ⟨i, hq.pderiv, hi, ?_⟩
  intro hm
  have hdiv : q ∣ pderiv i q := Ideal.mem_span_singleton.mp hm
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hi
  have hderiv := (hq.pderiv (i := i)).totalDegree_le
  rw [hq.totalDegree hq0] at hle
  omega

theorem exists_quotient_section (I : Ideal (MvPolynomial σ F)) (d : ℕ) (hd : 0 < d)
    (q : MvPolynomial σ F) (hspan : I = Ideal.span {q}) (hq : q.IsHomogeneous d) (hq0 : q ≠ 0) :
    ∃ i, Ideal.Quotient.mk I (pderiv i q) ∈
      HomogeneousQuotientGrading.piece (homogeneousSubmodule σ F) I (d - 1) ∧
      Ideal.Quotient.mk I (pderiv i q) ≠ 0 := by
  obtain ⟨i, hh, _hi, hnot⟩ := exists_partial_not_mem d hd q hq hq0
  refine ⟨i, Submodule.mem_map.mpr ⟨pderiv i q, hh, rfl⟩, ?_⟩
  intro hz
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  rw [hspan] at hm
  exact hnot hm

end PaperP1.HomogeneousGradientSection
