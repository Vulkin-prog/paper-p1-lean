module

public import PaperP1.Geometry.OrdinarySurfaceCurveData
public import PaperP1.Arithmetic.OrdinaryIntegerPoints
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The explicit uniform affine-curve input on actual ordinary curve point sets

`UniformBound` is an explicit proposition recording the curve specialization
of Pila, Theorem A, Astérisque 228 (1995), pp. 183--187:
https://www.numdam.org/item/AST_1995__228__183_0.pdf .
All consequences below take a witness of this property as an argument. The
definition itself adds no axiom; a proof may be supplied by a separate count
on the actual prime/Hilbert presentation.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformAffineCurvePointCount

open PaperP1.OrdinarySurfaceCurveData PaperP1.OrdinaryIntegerPoints

def UniformBound (kmax M : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 0 < A ∧
    ∀ k : ℕ, k ≤ kmax → ∀ (c : Fin k → ℚ) (D : ℕ) (I J : Fin k → Finset ℤ),
    ∀ Γ : Curve c D I J, Γ.degree ≤ M → ∀ H : ℕ, 1 ≤ H →
      ((curvePoints Γ.ideal H).card : ℝ) ≤ A * (H : ℝ) ^ (1 / (Γ.degree : ℝ) + δ)

theorem high_degree_bound (kmax M E : ℕ) (hPila : UniformBound kmax M) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧
      ∀ k : ℕ, k ≤ kmax → ∀ (c : Fin k → ℚ) (D : ℕ) (I J : Fin k → Finset ℤ),
      ∀ Γ : Curve c D I J, Γ.degree ≤ M → E < Γ.degree → ∀ H : ℕ, 1 ≤ H →
        ((curvePoints Γ.ideal H).card : ℝ) ≤ A * (H : ℝ) ^ (1 / ((E : ℝ) + 1) + δ) := by
  obtain ⟨A, hA, hcount⟩ := hPila δ hδ
  refine ⟨A, hA, ?_⟩
  intro k hk c D I J Γ hM hgap H hH
  have hdegree : (E : ℝ) + 1 ≤ Γ.degree := by exact_mod_cast Nat.succ_le_iff.mpr hgap
  have hrecip : 1 / (Γ.degree : ℝ) ≤ 1 / ((E : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) hdegree
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  exact (hcount k hk c D I J Γ hM H hH).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hHreal (add_le_add hrecip (le_refl δ))) hA.le)

end PaperP1.UniformAffineCurvePointCount
