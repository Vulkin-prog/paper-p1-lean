module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Lean.Elab.Tactic.Omega

/-! # Factors of a nonzero homogeneous polynomial are homogeneous

The highest and lowest total degrees add in a domain. Embedding into formal
power series supplies the exact lowest-degree order without a cancellation
assumption on individual coefficients.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousFactorDegrees

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

theorem order_le_totalDegree (P : MvPolynomial σ R) (hP : P ≠ 0) :
    (P : MvPowerSeries σ R).order ≤ (P.totalDegree : ℕ∞) := by
  obtain ⟨m, hm⟩ := MvPolynomial.exists_coeff_ne_zero hP
  have hseries : MvPowerSeries.coeff m (P : MvPowerSeries σ R) ≠ 0 := by
    simpa only [MvPolynomial.coeff_coe] using hm
  have hdegree : Finsupp.degree m ≤ P.totalDegree :=
    MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hm)
  exact (MvPowerSeries.order_le hseries).trans (by exact_mod_cast hdegree)

theorem order_of_homogeneous (P : MvPolynomial σ R) (hP : P ≠ 0)
    (d : ℕ) (hd : P.IsHomogeneous d) : (P : MvPowerSeries σ R).order = d := by
  apply le_antisymm
  · exact (order_le_totalDegree P hP).trans_eq (by rw [hd.totalDegree hP])
  · apply MvPowerSeries.nat_le_order
    intro m hm
    rw [MvPolynomial.coeff_coe]
    by_contra hne
    have heq : Finsupp.degree m = d := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd hne
    omega

theorem homogeneous_of_order_eq_totalDegree (P : MvPolynomial σ R)
    (horder : (P : MvPowerSeries σ R).order = (P.totalDegree : ℕ∞)) :
    P.IsHomogeneous P.totalDegree := by
  intro m hm
  have hlo := MvPowerSeries.order_le
    (show MvPowerSeries.coeff m (P : MvPowerSeries σ R) ≠ 0 by
      simpa only [MvPolynomial.coeff_coe] using hm)
  rw [horder] at hlo
  have hlonat : P.totalDegree ≤ Finsupp.degree m := by exact_mod_cast hlo
  have hhi : Finsupp.degree m ≤ P.totalDegree :=
    MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hm)
  have heq := Nat.le_antisymm hhi hlonat
  rw [Finsupp.degree_eq_weight_one] at heq
  simpa only [Pi.one_def] using heq

variable [IsDomain R]

theorem homogeneous_factors (A B : MvPolynomial σ R) (hAB : A * B ≠ 0)
    (d : ℕ) (hd : (A * B).IsHomogeneous d) :
    A.IsHomogeneous A.totalDegree ∧ B.IsHomogeneous B.totalDegree := by
  have hA : A ≠ 0 := left_ne_zero_of_mul hAB
  have hB : B ≠ 0 := right_ne_zero_of_mul hAB
  have hAs : (A : MvPowerSeries σ R) ≠ 0 := MvPolynomial.coe_eq_zero_iff.not.mpr hA
  have hBs : (B : MvPowerSeries σ R) ≠ 0 := MvPolynomial.coe_eq_zero_iff.not.mpr hB
  let a := (A : MvPowerSeries σ R).order.toNat
  let b := (B : MvPowerSeries σ R).order.toNat
  have ha : (a : ℕ∞) = (A : MvPowerSeries σ R).order :=
    MvPowerSeries.ne_zero_iff_order_finite.mp hAs
  have hb : (b : ℕ∞) = (B : MvPowerSeries σ R).order :=
    MvPowerSeries.ne_zero_iff_order_finite.mp hBs
  have ha_le : a ≤ A.totalDegree := by
    exact_mod_cast (ha.trans_le (order_le_totalDegree A hA))
  have hb_le : b ≤ B.totalDegree := by
    exact_mod_cast (hb.trans_le (order_le_totalDegree B hB))
  have hab_order : (a : ℕ∞) + b = (d : ℕ∞) := by
    rw [ha, hb, ← MvPowerSeries.order_mul, ← MvPolynomial.coe_mul]
    exact order_of_homogeneous (A * B) hAB d hd
  have hab : a + b = d := by exact_mod_cast hab_order
  have hdegree : A.totalDegree + B.totalDegree = d := by
    rw [← MvPolynomial.totalDegree_mul_of_isDomain hA hB]
    exact hd.totalDegree hAB
  have hea : a = A.totalDegree := by omega
  have heb : b = B.totalDegree := by omega
  exact ⟨homogeneous_of_order_eq_totalDegree A (ha.symm.trans (by rw [hea])),
    homogeneous_of_order_eq_totalDegree B (hb.symm.trans (by rw [heb]))⟩

end PaperP1.HomogeneousFactorDegrees
