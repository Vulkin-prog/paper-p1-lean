module

public import PaperP1.Analysis.ReducedDeterminantCosts
public import PaperP1.Asymptotics.WeightedReducedFamilyCount

/-! # Count every actual gcd family at the original costs with a separately weakened barrier -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedOriginalScaleFamilyCount

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantSourceBox
open PaperP1.IntegralSourceCoefficients PaperP1.ActualSourcePrimitiveReduction
open PaperP1.ReducedDyadicScales PaperP1.ReducedSourceParameter PaperP1.DeterminantLogScale

theorem uniform_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (δ C ρ Kbar Abar K A ε : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hKbar : 0 ≤ Kbar) (hAbar : 0 ≤ Abar) (hK : 0 ≤ K) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℕ, 0 < h → (h : ℝ) ≤ K * (Real.log N) ^ A →
      ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X, ∀ Γ : ℝ, 0 ≤ Γ → Γ ≤ Kbar * (Real.log N) ^ Abar →
      (N : ℝ) ≤ Γ * X.c₁ * X.c₂ * (X.D * X.E) ^ 2 →
      ∀ S : Finset Quad, Population X h S → ∀ gq : ℕ × ℕ, (family gq S).Nonempty →
      ((family gq S).card : ℝ) ≤ (N : ℝ) ^ ε *
        min (Real.sqrt (X.D * X.E * Real.exp (logShape N X.D X.E X.U X.V)) + X.D + X.E)
          (Real.sqrt (X.U * X.V * Real.exp (logShape N X.D X.E X.U X.V)) + X.U + X.V) := by
  obtain ⟨Nf, hf⟩ := WeightedReducedFamilyCount.uniform_count hHB hNG δ C ρ Kbar Abar K A (ε / 2)
    hδ hC hρ hρ₁ hKbar hAbar hK hA (by positivity)
  obtain ⟨Nc, hc⟩ := ReducedDeterminantCosts.uniform_cost_comparison C K A (ε / 2) hC (by positivity)
  refine ⟨max 1 (max Nf Nc), ?_⟩
  intro N hN h hh hshift X coefs Γ hΓ hΓbudget hbarrier S hS gq hne
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hmem, hs, _hdivpos, _hdivle, hscale⟩ := family_shift_bounds coefs hh hS gq hne
  have hg : 0 < gq.1 := (mem_Icc.mp (mem_product.mp (mem_filter.mp hmem).1).1).1
  have hq : 0 < gq.2 := (mem_Icc.mp (mem_product.mp (mem_filter.mp hmem).1).2).1
  let N' := parameter N (gq.1 ^ 2 * gq.2)
  let D' := enlarged X.D gq.1
  let E' := enlarged X.E gq.1
  let U' := enlarged X.U gq.2
  let V' := enlarged X.V gq.2
  let F' := Real.exp (logShape N' D' E' U' V')
  let F := Real.exp (logShape N X.D X.E X.U X.V)
  let cost := min (Real.sqrt (X.D * X.E * F) + X.D + X.E) (Real.sqrt (X.U * X.V * F) + X.U + X.V)
  let cost' := min (Real.sqrt (D' * E' * F') + D' + E') (Real.sqrt (U' * V' * F') + U' + V')
  have hcount : ((family gq S).card : ℝ) ≤ (N' : ℝ) ^ (ε / 2) * cost' :=
    hf N (by omega) h hh hshift X coefs Γ hΓ hΓbudget hbarrier S hS gq hne
  obtain ⟨hc₁, hc₂⟩ := hc N (by omega) h hh hshift ρ δ X gq.1 gq.2 hg hq hscale
  have hcost : cost' ≤ (N : ℝ) ^ (ε / 2) * cost := by
    dsimp only [cost', cost]
    rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg hn.le (ε / 2))]
    exact min_le_min hc₁ hc₂
  have hcost' : 0 ≤ cost' := by
    have hD := enlarged_ge_one X.D gq.1
    have hE := enlarged_ge_one X.E gq.1
    have hU := enlarged_ge_one X.U gq.2
    have hV := enlarged_ge_one X.V gq.2
    dsimp only [cost', D', E', U', V']
    apply le_min <;> positivity
  have hparam : (N' : ℝ) ≤ N := by exact_mod_cast parameter_le_original N (gq.1 ^ 2 * gq.2) hs
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg N') hparam (show 0 ≤ ε / 2 by positivity)
  change ((family gq S).card : ℝ) ≤ (N : ℝ) ^ ε * cost
  calc
    _ ≤ (N' : ℝ) ^ (ε / 2) * cost' := hcount
    _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * cost) :=
      mul_le_mul hpow hcost hcost' (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← mul_assoc, ← Real.rpow_add hn]; congr 2; ring

end PaperP1.WeightedOriginalScaleFamilyCount
