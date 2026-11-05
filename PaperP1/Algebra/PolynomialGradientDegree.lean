module

public import PaperP1.Algebra.PolynomialTangentDegree
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Push

/-! # Strict partial-derivative degree and a nonzero gradient polynomial

Every nonconstant real plane polynomial has an actual nonzero formal partial.
The degree drop makes that partial independent of an irreducible equation.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialGradientDegree

open MvPolynomial

theorem pderiv_degree_le_sub_one {R σ : Type*} [CommRing R] (P : MvPolynomial σ R) (i : σ) :
    (pderiv i P).totalDegree ≤ P.totalDegree - 1 := by
  classical
  apply Finset.sup_le
  intro m hm
  have hc := MvPolynomial.mem_support_iff.mp hm
  rw [coeff_pderiv] at hc
  have hcoeff : P.coeff (m + Finsupp.single i 1) ≠ 0 := left_ne_zero_of_mul hc
  have hd := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)
  have he : (m + Finsupp.single i 1).sum (fun _ e ↦ e) = m.sum (fun _ e ↦ e) + 1 := by
    simp [Finsupp.sum_add_index']
  omega

theorem exists_nonzero_partial (P : MvPolynomial (Fin 2) ℝ) (hdegree : 0 < P.totalDegree) :
    ∃ i : Fin 2, pderiv i P ≠ 0 := by
  classical
  have hex : ∃ m ∈ P.support, 0 < m.sum (fun _ e ↦ e) := by
    by_contra hbad
    push Not at hbad
    have hz : P.totalDegree ≤ 0 := Finset.sup_le (fun m hm ↦ hbad m hm)
    omega
  obtain ⟨m, hm, hmpos⟩ := hex
  have he : m = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) := by
    ext i
    fin_cases i <;> simp
  have hs : m.sum (fun _ e ↦ e) = m 0 + m 1 := by
    calc
      _ = (Finsupp.single (0 : Fin 2) (m 0) + Finsupp.single 1 (m 1)).sum (fun _ e ↦ e) :=
        congrArg (fun v : Fin 2 →₀ ℕ ↦ v.sum (fun _ e ↦ e)) he
      _ = _ := by simp [Finsupp.sum_add_index']
  have hi : ∃ i : Fin 2, m i ≠ 0 := by
    by_cases hz : m 0 = 0
    · exact ⟨1, by omega⟩
    · exact ⟨0, hz⟩
  obtain ⟨i, hi⟩ := hi
  let q := m - Finsupp.single i 1
  have hq : q + Finsupp.single i 1 = m := Finsupp.sub_add_single_one_cancel hi
  have hc : (pderiv i P).coeff q ≠ 0 := by
    rw [coeff_pderiv, hq]
    have hn : (((q i + 1 : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hm) (by simpa only [Nat.cast_add, Nat.cast_one] using hn)
  refine ⟨i, ?_⟩
  intro hz
  exact hc (by simp [hz])

theorem exists_partial_not_dvd (P : MvPolynomial (Fin 2) ℝ) (hdegree : 0 < P.totalDegree) :
    ∃ i : Fin 2, pderiv i P ≠ 0 ∧ ¬P ∣ pderiv i P := by
  obtain ⟨i, hi⟩ := exists_nonzero_partial P hdegree
  refine ⟨i, hi, ?_⟩
  intro hdiv
  have hd := totalDegree_le_of_dvd_of_isDomain hdiv hi
  have hp := pderiv_degree_le_sub_one P i
  omega

end PaperP1.PolynomialGradientDegree
