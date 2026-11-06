module

public import PaperP1.Algebra.SmoothSurfaceDeterminant
public import PaperP1.Algebra.TernaryMvPolynomialEvaluation
public import PaperP1.Algebra.CoordinateSwapEvaluation

/-! # Actual smooth three-coordinate surface determinants in every coordinate orientation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineSurfaceDeterminant

open MvPolynomial

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

theorem nilpotent_dvd (p : R) (N : ℕ) (hN : (Ideal.span {p} : Ideal R) ^ N = ⊥)
    (P : MvPolynomial (Fin 3) R) (a : Fin 3 → R)
    (hP : eval a P ∈ Ideal.span {p})
    (hder : IsUnit (Ideal.Quotient.mk (Ideal.span {p}) (eval a (pderiv 2 P))))
    (L : ℕ) (v : ι → Fin 3 → R) (hv : ∀ j k, p ∣ v j k - a k)
    (hroots : ∀ j, eval (v j) P = 0) (F : ι → MvPolynomial (Fin 3) R) :
    p ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ Matrix.det (fun i j ↦ eval (v j) (F i)) := by
  have ha : ![a 0, a 1, a 2] = a := by ext i; fin_cases i <;> rfl
  have hv' (j : ι) : ![v j 0, v j 1, v j 2] = v j := by ext i; fin_cases i <;> rfl
  have hd := SmoothSurfaceDeterminant.nilpotent_surface_dvd p N hN
    (TernaryMvPolynomialEvaluation.iterated P) (a 0) (a 1) (a 2)
    (by simpa only [TernaryMvPolynomialEvaluation.evaluation, ha] using hP)
    (by simpa only [TernaryMvPolynomialEvaluation.derivative,
      TernaryMvPolynomialEvaluation.evaluation, ha] using hder)
    L (fun j ↦ v j 0) (fun j ↦ v j 1) (fun j ↦ v j 2)
    (fun j ↦ hv j 0) (fun j ↦ hv j 1) (fun j ↦ hv j 2)
    (by simpa only [TernaryMvPolynomialEvaluation.evaluation, hv'] using hroots)
    (fun i ↦ TernaryMvPolynomialEvaluation.iterated (F i))
  simpa only [TernaryMvPolynomialEvaluation.evaluation, hv'] using hd

theorem integer_dvd_last (p L : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 3) ℤ) (a : Fin 3 → ℤ)
    (hP : (p : ℤ) ∣ eval a P) (hder : ¬(p : ℤ) ∣ eval a (pderiv 2 P))
    (v : ι → Fin 3 → ℤ) (hv : ∀ j k, (p : ℤ) ∣ v j k - a k)
    (hroots : ∀ j, eval (v j) P = 0) (F : ι → MvPolynomial (Fin 3) ℤ) :
    (p : ℤ) ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ Matrix.det (fun i j ↦ eval (v j) (F i)) := by
  have ha : ![a 0, a 1, a 2] = a := by ext i; fin_cases i <;> rfl
  have hv' (j : ι) : ![v j 0, v j 1, v j 2] = v j := by ext i; fin_cases i <;> rfl
  have hd := SmoothSurfaceDeterminant.integer_smooth_dvd p L hp
    (TernaryMvPolynomialEvaluation.iterated P) (a 0) (a 1) (a 2)
    (by simpa only [TernaryMvPolynomialEvaluation.evaluation, ha] using hP)
    (by simpa only [TernaryMvPolynomialEvaluation.derivative,
      TernaryMvPolynomialEvaluation.evaluation, ha] using hder)
    (fun j ↦ v j 0) (fun j ↦ v j 1) (fun j ↦ v j 2)
    (fun j ↦ hv j 0) (fun j ↦ hv j 1) (fun j ↦ hv j 2)
    (by simpa only [TernaryMvPolynomialEvaluation.evaluation, hv'] using hroots)
    (fun i ↦ TernaryMvPolynomialEvaluation.iterated (F i))
  simpa only [TernaryMvPolynomialEvaluation.evaluation, hv'] using hd

theorem integer_dvd (p L : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 3) ℤ) (a : Fin 3 → ℤ)
    (hP : (p : ℤ) ∣ eval a P) (hgrad : ∃ k, ¬(p : ℤ) ∣ eval a (pderiv k P))
    (v : ι → Fin 3 → ℤ) (hv : ∀ j k, (p : ℤ) ∣ v j k - a k)
    (hroots : ∀ j, eval (v j) P = 0) (F : ι → MvPolynomial (Fin 3) ℤ) :
    (p : ℤ) ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ Matrix.det (fun i j ↦ eval (v j) (F i)) := by
  obtain ⟨k, hk⟩ := hgrad
  let e := Equiv.swap k (2 : Fin 3)
  have hPe : (p : ℤ) ∣ eval (fun i ↦ a (e i)) (rename e P) := by
    simpa only [e, CoordinateSwapEvaluation.evaluation] using hP
  have hde : ¬(p : ℤ) ∣ eval (fun i ↦ a (e i)) (pderiv 2 (rename e P)) := by
    simpa only [e, CoordinateSwapEvaluation.evaluation_partial] using hk
  have hd := integer_dvd_last p L hp (rename e P) (fun i ↦ a (e i)) hPe hde
    (fun j i ↦ v j (e i)) (fun j i ↦ hv j (e i))
    (by simpa only [e, CoordinateSwapEvaluation.evaluation] using hroots)
    (fun i ↦ rename e (F i))
  simpa only [e, CoordinateSwapEvaluation.evaluation] using hd

end PaperP1.AffineSurfaceDeterminant
