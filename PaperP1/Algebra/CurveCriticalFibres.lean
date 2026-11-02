module

public import PaperP1.Algebra.BivariateCurveDegrees
public import PaperP1.Algebra.BivariateResultantHeight
public import PaperP1.Algebra.BivariateResultantNonzero
public import Mathlib.Algebra.Polynomial.Roots

/-! # Actual exceptional integer fibres of the irreducible curve -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveCriticalFibres

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree PaperP1.BivariateCurveDegrees

def criticalPolynomial (P : ℤ[X][X]) : ℤ[X] := P.leadingCoeff * P.resultant P.derivative

theorem critical_nonzero (P : ℤ[X][X]) (hP : Irreducible P) (hy : 0 < degreeY P) :
    criticalPolynomial P ≠ 0 := by
  have hderiv : P.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (ne_of_gt hy)
  have hnot : ¬ P ∣ P.derivative := by
    intro h
    exact (not_lt_of_ge (Polynomial.natDegree_le_of_dvd h hderiv))
      (Polynomial.natDegree_derivative_lt (ne_of_gt hy))
  exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP.ne_zero)
    (BivariateResultantNonzero.nonzero_of_not_dvd P P.derivative hP hy hnot)

theorem critical_degree (P : ℤ[X][X]) :
    (criticalPolynomial P).natDegree ≤ degreeX P + 2 * degreeX P * degreeY P := by
  have hl : P.leadingCoeff.natDegree ≤ degreeX P := by
    simpa only [coeff_natDegree] using natDegree_coeff_le_degreeX P P.natDegree
  have hr := BivariateResultantHeight.resultant_degree P P.derivative P.natDegree P.derivative.natDegree
    (degreeX P) le_rfl (degreeX_derivative_le P)
  have hd : P.derivative.natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_derivative_le P).trans (Nat.sub_le _ _)
  have hn : P.natDegree + P.derivative.natDegree ≤ 2 * degreeY P := by
    change P.natDegree + P.derivative.natDegree ≤ 2 * P.natDegree
    omega
  calc
    _ ≤ P.leadingCoeff.natDegree + (P.resultant P.derivative).natDegree := natDegree_mul_le
    _ ≤ degreeX P + (P.natDegree + P.derivative.natDegree) * degreeX P := Nat.add_le_add hl hr
    _ ≤ degreeX P + (2 * degreeY P) * degreeX P := Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) _
    _ = _ := by ring

def badOffsets (P : ℤ[X][X]) : Finset ℤ := (criticalPolynomial P).roots.toFinset.image (fun z ↦ -z)

theorem mem_badOffsets_iff (P : ℤ[X][X]) (hP : Irreducible P) (hy : 0 < degreeY P) (u : ℤ) :
    u ∈ badOffsets P ↔ (criticalPolynomial P).eval (-u) = 0 := by
  rw [badOffsets, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, he⟩
    have hr : (criticalPolynomial P).eval v = 0 :=
      (Polynomial.mem_roots (critical_nonzero P hP hy)).mp (Multiset.mem_toFinset.mp hv)
    have hvu : v = -u := by omega
    rwa [hvu] at hr
  · intro hu
    refine ⟨-u, ?_, neg_neg u⟩
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (critical_nonzero P hP hy)).mpr hu)

theorem regular_iff (P : ℤ[X][X]) (hP : Irreducible P) (hy : 0 < degreeY P) (u : ℤ) :
    u ∉ badOffsets P ↔ P.leadingCoeff.eval (-u) ≠ 0 ∧ (P.resultant P.derivative).eval (-u) ≠ 0 := by
  rw [mem_badOffsets_iff P hP hy u]
  simp only [criticalPolynomial, eval_mul, mul_eq_zero, not_or]

theorem badOffsets_card (P : ℤ[X][X]) :
    (badOffsets P).card ≤ degreeX P + 2 * degreeX P * degreeY P := by
  calc
    _ ≤ (criticalPolynomial P).roots.toFinset.card := Finset.card_image_le
    _ ≤ (criticalPolynomial P).roots.card := Multiset.toFinset_card_le _
    _ ≤ (criticalPolynomial P).natDegree := Polynomial.card_roots' _
    _ ≤ _ := critical_degree P

theorem swapped_critical_nonzero (P : ℤ[X][X]) (hP : Irreducible P) (hx : 0 < degreeX P) :
    criticalPolynomial (Bivariate.swap P) ≠ 0 := by
  apply critical_nonzero
  · exact hP.map (Bivariate.swap (R := ℤ))
  · rwa [degreeY_swap]

theorem exceptional_budget (P : ℤ[X][X]) (hy : 0 < degreeY P) :
    (badOffsets P).card + (badOffsets (Bivariate.swap P)).card ≤ 6 * totalDegree P ^ 2 := by
  have hxD := degreeX_le_total P
  have hyD := degreeY_le_total P
  have hD : 1 ≤ totalDegree P := by omega
  have hDsq : totalDegree P ≤ totalDegree P ^ 2 := by
    simpa only [mul_one, pow_two] using Nat.mul_le_mul_left (totalDegree P) hD
  have h₁ := badOffsets_card P
  have h₂ := badOffsets_card (Bivariate.swap P)
  rw [degreeX_swap, degreeY_swap] at h₂
  have hp : degreeX P * degreeY P ≤ totalDegree P * totalDegree P := Nat.mul_le_mul hxD hyD
  nlinarith

end PaperP1.CurveCriticalFibres
