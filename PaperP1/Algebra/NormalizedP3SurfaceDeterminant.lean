module

public import PaperP1.Algebra.AffineSurfaceDeterminant
public import PaperP1.Algebra.LastChartPolynomial
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Tactic.Push

/-! # Actual smooth P³ hypersurface determinant divisors on the original integer chart X₃ = 1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedP3SurfaceDeterminant

open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem free_partial (p d : ℕ) (P : MvPolynomial (Fin 4) ℤ) (hhom : P.IsHomogeneous d)
    (a : Fin 4 → ℤ) (ha : a 3 = 1) (hP : (p : ℤ) ∣ eval a P)
    (hgrad : ∃ k, ¬(p : ℤ) ∣ eval a (pderiv k P)) :
    ∃ k : Fin 3, ¬(p : ℤ) ∣ eval a (pderiv k.castSucc P) := by
  classical
  by_contra hn
  push Not at hn
  have he := congrArg (eval a) hhom.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul, map_natCast] at he
  have haLast : a (Fin.last 3) = 1 := ha
  rw [Fin.sum_univ_castSucc, haLast, one_mul] at he
  have hsum : (p : ℤ) ∣ ∑ k : Fin 3, a k.castSucc * eval a (pderiv k.castSucc P) :=
    Finset.dvd_sum (fun k _ ↦ dvd_mul_of_dvd_right (hn k) _)
  have hlast : (p : ℤ) ∣ eval a (pderiv 3 P) := by
    have hd := dvd_sub (dvd_mul_of_dvd_right hP (d : ℤ)) hsum
    rw [← he, add_sub_cancel_left] at hd
    exact hd
  obtain ⟨k, hk⟩ := hgrad
  apply hk
  cases k using Fin.lastCases with
  | last => exact hlast
  | cast k => exact hn k

theorem integer_dvd (p L d : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ)
    (hhom : P.IsHomogeneous d) (a : Fin 4 → ℤ) (ha : a 3 = 1)
    (hP : (p : ℤ) ∣ eval a P) (hgrad : ∃ k, ¬(p : ℤ) ∣ eval a (pderiv k P))
    (v : ι → Fin 4 → ℤ) (hvlast : ∀ j, v j 3 = 1)
    (hv : ∀ j k, (p : ℤ) ∣ v j k - a k)
    (hroots : ∀ j, eval (v j) P = 0) (F : ι → MvPolynomial (Fin 4) ℤ) :
    (p : ℤ) ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ Matrix.det (fun i j ↦ eval (v j) (F i)) := by
  have ha' : Fin.snoc (fun k : Fin 3 ↦ a k.castSucc) 1 = a := by
    funext k
    cases k using Fin.lastCases with
    | last => exact (Fin.snoc_last _ _).trans ha.symm
    | cast k => exact Fin.snoc_castSucc _ _ k
  have hv' (j : ι) : Fin.snoc (fun k : Fin 3 ↦ v j k.castSucc) 1 = v j := by
    funext k
    cases k using Fin.lastCases with
    | last => exact (Fin.snoc_last _ _).trans (hvlast j).symm
    | cast k => exact Fin.snoc_castSucc _ _ k
  have hbase : (p : ℤ) ∣ eval (fun k : Fin 3 ↦ a k.castSucc) (LastChartPolynomial.dehomogenize P) := by
    simpa only [LastChartPolynomial.evaluation, ha'] using hP
  have hder : ∃ k, ¬(p : ℤ) ∣ eval (fun k : Fin 3 ↦ a k.castSucc)
      (pderiv k (LastChartPolynomial.dehomogenize P)) := by
    obtain ⟨k, hk⟩ := free_partial p d P hhom a ha hP hgrad
    refine ⟨k, ?_⟩
    simpa only [LastChartPolynomial.pderiv, LastChartPolynomial.evaluation, ha'] using hk
  have hd := AffineSurfaceDeterminant.integer_dvd p L hp (LastChartPolynomial.dehomogenize P)
    (fun k : Fin 3 ↦ a k.castSucc) hbase hder (fun j k ↦ v j k.castSucc)
    (fun j k ↦ hv j k.castSucc)
    (by simpa only [LastChartPolynomial.evaluation, hv'] using hroots)
    (fun i ↦ LastChartPolynomial.dehomogenize (F i))
  simpa only [LastChartPolynomial.evaluation, hv'] using hd

end PaperP1.NormalizedP3SurfaceDeterminant
