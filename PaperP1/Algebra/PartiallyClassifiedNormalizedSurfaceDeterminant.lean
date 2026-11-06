module

public import PaperP1.Algebra.PartiallyClassifiedBivariateDeterminant
public import PaperP1.Algebra.SmoothSurfacePolynomialApproximation

/-! # Smooth residue classes contribute to the original determinant even when other columns reduce nonsmoothly -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PartiallyClassifiedNormalizedSurfaceDeterminant

open MvPolynomial Finset

variable {ι χ : Type*} [Fintype ι] [DecidableEq ι] [Fintype χ] [DecidableEq χ]

theorem integer_dvd (p d : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ)
    (hhom : P.IsHomogeneous d) (a : χ → Fin 4 → ℤ) (ha : ∀ c, a c 3 = 1)
    (hP : ∀ c, (p : ℤ) ∣ eval (a c) P)
    (hgrad : ∀ c, ∃ k, ¬(p : ℤ) ∣ eval (a c) (pderiv k P))
    (b : ι → Option χ) (L : χ → ℕ) (v : ι → Fin 4 → ℤ) (hvlast : ∀ j, v j 3 = 1)
    (hv : ∀ j c, b j = some c → ∀ k, (p : ℤ) ∣ v j k - a c k)
    (hroots : ∀ j, eval (v j) P = 0) (F : ι → MvPolynomial (Fin 4) ℤ) :
    (p : ℤ) ^ (∑ c, (L c * Fintype.card {j // b j = some c} - (L c + 2).choose 3)) ∣
      Matrix.det (fun i j ↦ eval (v j) (F i)) := by
  classical
  let E := ∑ c, (L c * Fintype.card {j // b j = some c} - (L c + 2).choose 3)
  have happrox (c : χ) := SmoothSurfacePolynomialApproximation.normalized_integer
    p E d hp P hhom (a c) (ha c) (hP c) (hgrad c)
  choose x y T hT using happrox
  let Q : χ → ι → MvPolynomial (Fin 2) ℤ := fun c i ↦ T c (F i)
  let X : ι → ℤ := fun j ↦ (b j).elim 0 (fun c ↦ x c (v j))
  let Y : ι → ℤ := fun j ↦ (b j).elim 0 (fun c ↦ y c (v j))
  have hX (j : ι) (c : χ) (hb : b j = some c) : X j = x c (v j) := by simp [X, hb]
  have hY (j : ι) (c : χ) (hb : b j = some c) : Y j = y c (v j) := by simp [Y, hb]
  have hdata (j : ι) (c : χ) (hb : b j = some c) :=
    hT c (v j) (hvlast j) (hv j c hb) (hroots j)
  apply PartiallyClassifiedBivariateDeterminant.congruent_polynomial_dvd (p : ℤ) Q b L X Y
    (fun i j ↦ eval (v j) (F i))
  · intro j c hb
    rw [hX j c hb]
    exact (hdata j c hb).1
  · intro j c hb
    rw [hY j c hb]
    exact (hdata j c hb).2.1
  · intro i j c hb
    rw [hX j c hb, hY j c hb]
    exact (hdata j c hb).2.2 (F i)

end PaperP1.PartiallyClassifiedNormalizedSurfaceDeterminant
