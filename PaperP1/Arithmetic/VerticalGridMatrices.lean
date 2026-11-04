module

public import PaperP1.Arithmetic.ActualVerticalLattice

/-! # Actual vertical matrices indexed consistently by the quadratic grid -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.VerticalGridMatrices

open PaperP1.DeterminantSourceBox PaperP1.EffectiveSourceCoordinates

def gridTransform {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (M q : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let U := scale N X.c₁ X.D
  let V := scale N X.c₂ X.E
  PaperP1.RelativeIntervalLattice.transform (2 * C * V) (C * U) (2 * M)
    (PaperP1.DeterminantRelativeIntervals.intervalCenter (2 * M) (2 * C * V) (C * U) q)

theorem actual_transform_eq {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (M k : ℕ) :
    ActualVerticalLattice.transform X M k = gridTransform X M (QuadraticIntervalGrid.grid M k) := rfl

theorem inflated_scale_bounds {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ)
    (hN : 0 < N) (hC : 0 < C) :
    1 ≤ 2 * C * scale N X.c₂ X.E ∧ 1 ≤ C * scale N X.c₁ X.D ∧
      2 * C * scale N X.c₂ X.E ≤ 2 * C * N ∧ C * scale N X.c₁ X.D ≤ C * N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hU := scale_bounds hn X.c₁_ge_one X.D_ge_one X.U_ge_one X.first_lower X.first_upper
  have hV := scale_bounds hn X.c₂_ge_one X.E_ge_one X.V_ge_one X.second_lower X.second_upper
  refine ⟨by linarith [hV.2.2.2.2], hU.2.2.2.2, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_left hV.2.1 (by positivity)
  · exact mul_le_mul_of_nonneg_left hU.2.1 hC.le

theorem effective_pair_product_bound {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ)
    (hN : 0 < N) (hρ : 0 < ρ) :
    scale N X.c₁ X.D * scale N X.c₂ X.E ≤ (X.U * X.V) / ρ ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hU := scale_bounds hn X.c₁_ge_one X.D_ge_one X.U_ge_one X.first_lower X.first_upper
  have hV := scale_bounds hn X.c₂_ge_one X.E_ge_one X.V_ge_one X.second_lower X.second_upper
  have hm := mul_le_mul hU.2.2.2.1 hV.2.2.2.1 (mul_pos hρ hV.1).le (by linarith [X.U_ge_one])
  apply (le_div_iff₀ (sq_pos_of_pos hρ)).mpr
  nlinarith only [hm]

end PaperP1.VerticalGridMatrices
