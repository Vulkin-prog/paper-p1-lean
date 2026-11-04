module

public import PaperP1.Arithmetic.VerticalGridMatrices
public import PaperP1.Asymptotics.QuadraticGridRadiusSum

/-! # Actual vertical side summation expressed in the original source scales U,V -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveVerticalSideSum

open Finset PaperP1.DeterminantSourceBox PaperP1.EffectiveSourceCoordinates
open PaperP1.RelativeIntervalLattice PaperP1.DeterminantRelativeIntervals
open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction PaperP1.BinaryLatticeCoordinateBounds
open PaperP1.QuadraticIntervalGrid

theorem effective_upper_bounds {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ)
    (hN : 0 < N) (hρ : 0 < ρ) :
    scale N X.c₁ X.D ≤ X.U / ρ ∧ scale N X.c₂ X.E ≤ X.V / ρ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hU := scale_bounds hn X.c₁_ge_one X.D_ge_one X.U_ge_one X.first_lower X.first_upper
  have hV := scale_bounds hn X.c₂_ge_one X.E_ge_one X.V_ge_one X.second_lower X.second_upper
  constructor
  · apply (le_div_iff₀ hρ).mpr
    nlinarith only [hU.2.2.2.1]
  · apply (le_div_iff₀ hρ).mpr
    nlinarith only [hV.2.2.2.1]

theorem quadratic_sqrt_bound {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ)
    (hN : 0 < N) (hC : 0 < C) (hρ : 0 < ρ) (M : ℕ) :
    Real.sqrt ((2 * C * scale N X.c₂ X.E) * (C * scale N X.c₁ X.D) * (2 * M)) ≤
      (2 * C / ρ) * Real.sqrt (X.U * X.V * M) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hU := scale_bounds hn X.c₁_ge_one X.D_ge_one X.U_ge_one X.first_lower X.first_upper
  have hV := scale_bounds hn X.c₂_ge_one X.E_ge_one X.V_ge_one X.second_lower X.second_upper
  have hUp := hU.1
  have hVp := hV.1
  have hUV : 0 ≤ X.U * X.V * (M : ℝ) := by
    have hu : 0 ≤ X.U := by linarith [X.U_ge_one]
    have hv : 0 ≤ X.V := by linarith [X.V_ge_one]
    positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity)]
  calc
    _ = (4 * C ^ 2 * M) * (scale N X.c₁ X.D * scale N X.c₂ X.E) := by ring
    _ ≤ (4 * C ^ 2 * M) * ((X.U * X.V) / ρ ^ 2) :=
      mul_le_mul_of_nonneg_left (VerticalGridMatrices.effective_pair_product_bound X hN hρ) (by positivity)
    _ = _ := by rw [mul_pow, div_pow, Real.sq_sqrt hUV]; ring

theorem numerical_cost_bound {a S U V C ρ R : ℝ} (ha : 1 ≤ a) (hS : 0 ≤ S)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hC : 0 < C) (hρ : 0 < ρ) (hR : 0 ≤ R) :
    (R / 2) * (120 * a * ((2 * C / ρ) * S) + 1024 * (C * (U / ρ)) + 16 * (2 * C * (V / ρ))) ≤
      (512 * R * C / ρ) * a * (S + U + V) := by
  have ha0 : 0 ≤ a := by linarith
  have hUS : U ≤ a * U := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) hU]
  have hVS : V ≤ a * V := by nlinarith [mul_nonneg (sub_nonneg.mpr ha) hV]
  calc
    _ = (R * C / ρ) * (120 * a * S + 512 * U + 16 * V) := by ring
    _ ≤ (R * C / ρ) * (512 * a * (S + U + V)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg ha0 hS, mul_nonneg ha0 hV]
    _ = _ := by ring

theorem uniform_original_scale_sum (κ : ℕ) (ε C ρ : ℝ) (hε : 0 < ε) (hC : 0 < C) (hρ : 0 < ρ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 32 ≤ M → 2 * M ≤ N →
      ∀ δ : ℝ, ∀ X : Box N ρ C δ, ∀ I : Finset ℕ,
      (∀ k ∈ I, M ≤ 4 * k) → (∀ k ∈ I, k ≤ 2 * M) → ∀ z : ℕ → Fin 2 → ℤ,
      (∀ q ∈ I.image (grid M), (z q 0).natAbs.Coprime (z q 1).natAbs) →
      (∀ q ∈ I.image (grid M), (z q 1).natAbs ≤ N ^ κ) →
      let R := 2 * (49 + 16 / ρ)
      let L := fun q ↦ sideLength R (squareNorm (realImage (VerticalGridMatrices.gridTransform X M q) (z q)))
      (∑ k ∈ I, L (grid M k)) ≤
        (512 * R * C / ρ) * (N : ℝ) ^ ε * (Real.sqrt (X.U * X.V * M) + X.U + X.V) := by
  obtain ⟨N₀, hsum⟩ := QuadraticGridRadiusSum.uniform_radius_sum κ ε hε
  refine ⟨N₀, ?_⟩
  intro N hN M hM hMN δ X I hlow hupper z hprimitive hheight
  have hNp : 0 < N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast hNp
  have hU := scale_bounds hn X.c₁_ge_one X.D_ge_one X.U_ge_one X.first_lower X.first_upper
  have hV := scale_bounds hn X.c₂_ge_one X.E_ge_one X.V_ge_one X.second_lower X.second_upper
  let U := scale N X.c₁ X.D
  let V := scale N X.c₂ X.E
  let R := 2 * (49 + 16 / ρ)
  have hUp : 0 < U := hU.1
  have hVp : 0 < V := hV.1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hb := hsum N hN M hM hMN (2 * C * V) (C * U) (by positivity) (by positivity)
    I hlow hupper z hprimitive hheight R hR
  have hsqrt := quadratic_sqrt_bound X hNp hC hρ M
  have hscales := effective_upper_bounds X hNp hρ
  have ha : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow
    (by exact_mod_cast (show 1 ≤ N by omega)) hε.le
  have hu : 0 ≤ X.U := by linarith [X.U_ge_one]
  have hv : 0 ≤ X.V := by linarith [X.V_ge_one]
  have hcost : (R / 2) *
      (120 * (N : ℝ) ^ ε * Real.sqrt ((2 * C * V) * (C * U) * (2 * M)) + 1024 * (C * U) + 16 * (2 * C * V)) ≤
      (512 * R * C / ρ) * (N : ℝ) ^ ε * (Real.sqrt (X.U * X.V * M) + X.U + X.V) := by
    calc
      _ ≤ (R / 2) * (120 * (N : ℝ) ^ ε * ((2 * C / ρ) * Real.sqrt (X.U * X.V * M)) +
          1024 * (C * (X.U / ρ)) + 16 * (2 * C * (X.V / ρ))) := by
        gcongr
        · exact hscales.1
        · exact hscales.2
      _ ≤ _ := numerical_cost_bound ha (Real.sqrt_nonneg _) hu hv hC hρ hR
  change (∑ k ∈ I, sideLength R _) ≤ _
  exact hb.trans hcost

end PaperP1.EffectiveVerticalSideSum
