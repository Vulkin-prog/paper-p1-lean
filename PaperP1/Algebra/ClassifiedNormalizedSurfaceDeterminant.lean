module

public import PaperP1.Algebra.ClassifiedBivariateDeterminant
public import PaperP1.Algebra.SmoothSurfacePolynomialApproximation

/-! # One original P³ surface determinant contains the sum of the contributions from distinct smooth classes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ClassifiedNormalizedSurfaceDeterminant

open MvPolynomial Finset

variable {ι χ : Type*} [Fintype ι] [DecidableEq ι] [Fintype χ] [DecidableEq χ]

theorem integer_dvd (p d : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ)
    (hhom : P.IsHomogeneous d) (a : χ → Fin 4 → ℤ) (ha : ∀ c, a c 3 = 1)
    (hP : ∀ c, (p : ℤ) ∣ eval (a c) P)
    (hgrad : ∀ c, ∃ k, ¬(p : ℤ) ∣ eval (a c) (pderiv k P))
    (b : ι → χ) (L : χ → ℕ) (v : ι → Fin 4 → ℤ) (hvlast : ∀ j, v j 3 = 1)
    (hv : ∀ j k, (p : ℤ) ∣ v j k - a (b j) k)
    (hroots : ∀ j, eval (v j) P = 0) (F : ι → MvPolynomial (Fin 4) ℤ) :
    (p : ℤ) ^ (∑ c, (L c * Fintype.card {j // b j = c} - (L c + 2).choose 3)) ∣
      Matrix.det (fun i j ↦ eval (v j) (F i)) := by
  classical
  let E := ∑ c, (L c * Fintype.card {j // b j = c} - (L c + 2).choose 3)
  have happrox (c : χ) := SmoothSurfacePolynomialApproximation.normalized_integer
    p E d hp P hhom (a c) (ha c) (hP c) (hgrad c)
  choose x y T hT using happrox
  let Q : χ → ι → MvPolynomial (Fin 2) ℤ := fun c i ↦ T c (F i)
  let X : ι → ℤ := fun j ↦ x (b j) (v j)
  let Y : ι → ℤ := fun j ↦ y (b j) (v j)
  have hdata (j : ι) := hT (b j) (v j) (hvlast j) (hv j) (hroots j)
  apply ClassifiedBivariateDeterminant.congruent_polynomial_dvd (p : ℤ) Q b L X Y
    (fun j ↦ (hdata j).1) (fun j ↦ (hdata j).2.1)
    (fun i j ↦ eval (v j) (F i))
  intro i j
  exact (hdata j).2.2 (F i)

end PaperP1.ClassifiedNormalizedSurfaceDeterminant
