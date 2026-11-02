module

public import PaperP1.Algebra.BivariateDegrees

/-! # Total degree of an actual nested integer polynomial and a nonzero coefficient attaining it -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateTotalDegree

open Polynomial PaperP1.BivariateDegrees

def totalDegree (P : ℤ[X][X]) : ℕ := P.support.sup (fun y ↦ y + (P.coeff y).natDegree)

theorem coefficient_degree_le (P : ℤ[X][X]) (x y : ℕ) (hc : (P.coeff y).coeff x ≠ 0) :
    x + y ≤ totalDegree P := by
  have hrow : P.coeff y ≠ 0 := fun h ↦ hc (by rw [h, coeff_zero])
  have hx := le_natDegree_of_ne_zero hc
  have hs := Finset.le_sup (f := fun i ↦ i + (P.coeff i).natDegree) (mem_support_iff.mpr hrow)
  unfold totalDegree
  omega

theorem exists_coefficient_degree (P : ℤ[X][X]) (hP : P ≠ 0) :
    ∃ x y : ℕ, (P.coeff y).coeff x ≠ 0 ∧ x + y = totalDegree P := by
  obtain ⟨y, hy, he⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.mpr hP)
    (fun i ↦ i + (P.coeff i).natDegree)
  have hrow : P.coeff y ≠ 0 := mem_support_iff.mp hy
  refine ⟨(P.coeff y).natDegree, y, ?_, ?_⟩
  · rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hrow
  · unfold totalDegree
    rw [he, add_comm]

theorem totalDegree_le_partial (P : ℤ[X][X]) : totalDegree P ≤ degreeX P + degreeY P := by
  apply Finset.sup_le
  intro y hy
  have hout : y ≤ degreeY P := le_natDegree_of_ne_zero (mem_support_iff.mp hy)
  have hin := natDegree_coeff_le_degreeX P y
  omega

theorem totalDegree_zero : totalDegree (0 : ℤ[X][X]) = 0 := by simp [totalDegree]

end PaperP1.BivariateTotalDegree
