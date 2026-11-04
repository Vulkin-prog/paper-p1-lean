module

public import PaperP1.Arithmetic.ActualReducedSourceBox
public import PaperP1.Analysis.ReducedSourceShiftBudget
public import PaperP1.Asymptotics.PrimitiveSourceDeterminantCount

/-! # Apply the full primitive determinant bound to every actual gcd-reduced family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualReducedFamilyCount

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.IntegralSourceCoefficients PaperP1.ActualProjectivePairs PaperP1.ActualSourcePrimitiveReduction
open PaperP1.ReducedDyadicScales PaperP1.ReducedSourceParameter PaperP1.ReducedSourceBarrier PaperP1.DeterminantLogScale

theorem uniform_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (δ C ρ K A ε : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℕ, 0 < h → (h : ℝ) ≤ K * (Real.log N) ^ A →
      ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      (N : ℝ) ≤ X.c₁ * X.c₂ * (X.D * X.E) ^ 2 →
      ∀ S : Finset Quad, Population X h S → ∀ gq : ℕ × ℕ, (family gq S).Nonempty →
      let N' := parameter N (gq.1 ^ 2 * gq.2)
      let D' := enlarged X.D gq.1
      let E' := enlarged X.E gq.1
      let U' := enlarged X.U gq.2
      let V' := enlarged X.V gq.2
      ((family gq S).card : ℝ) ≤ (N' : ℝ) ^ ε *
        min (Real.sqrt (D' * E' * Real.exp (logShape N' D' E' U' V')) + D' + E')
          (Real.sqrt (U' * V' * Real.exp (logShape N' D' E' U' V')) + U' + V') := by
  let K' := K * (2 : ℝ) ^ A
  have hK' : 0 ≤ K' := by dsimp [K']; positivity
  obtain ⟨L, hL⟩ := PrimitiveSourceDeterminantCount.uniform_primitive_count hHB hNG
    (δ / 2) (8 * C) (ρ / 2) (2 * K') A K' A ε
    (by positivity) (by positivity) (by positivity) (by linarith) (by positivity) hA hK' hA hε
  obtain ⟨Nb, hb⟩ := ActualReducedSourceBox.uniform_reduced_box δ C ρ K A hδ hC hρ L
  obtain ⟨Nm, hm⟩ := ReducedSourceLogarithms.uniform_shift_margin K A δ hδ
  refine ⟨max Nb Nm, ?_⟩
  intro N hN h hh hshift X coefs hbarrier S hS gq hne
  obtain ⟨hN1, hroot, _hlogh⟩ := hm N (by omega) h hh hshift
  obtain ⟨hmem, hs, _hdivpos, _hdivle, hscale⟩ := family_shift_bounds coefs hh hS gq hne
  have hg1 : 1 ≤ gq.1 := (mem_Icc.mp (mem_product.mp (mem_filter.mp hmem).1).1).1
  have hq1 : 1 ≤ gq.2 := (mem_Icc.mp (mem_product.mp (mem_filter.mp hmem).1).2).1
  have hg : 0 < gq.1 := by omega
  have hq : 0 < gq.2 := by omega
  let N' := parameter N (gq.1 ^ 2 * gq.2)
  let h' := h / (gq.1 ^ 2 * gq.2)
  obtain ⟨Y, hc₁, hc₂, hD, hE, hU, hV, hNL, hpop, hprim⟩ := hb N (by omega) h hh hshift X coefs S hS gq hne
  let dY : IntegerCoefficients Y := ActualReducedSourceBox.transfer_coefficients coefs hc₁ hc₂
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt N := by
    have hnR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have heq := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have hp := Real.sqrt_nonneg (N : ℝ)
    nlinarith
  have heff : 1 ≤ effective N (gq.1 ^ 2 * gq.2) :=
    hsqrt1.trans (effective_ge_sqrt N (gq.1 ^ 2 * gq.2) h hs hscale hroot)
  have hbarrierY : (N' : ℝ) ≤ loss gq.1 gq.2 * Y.c₁ * Y.c₂ * (Y.D * Y.E) ^ 2 := by
    rw [hc₁, hc₂, hD, hE]
    exact barrier_transfer N gq.1 gq.2 X.c₁ X.c₂ X.D X.E hg hq
      (by linarith [X.c₁_ge_one]) (by linarith [X.c₂_ge_one]) (by linarith [X.D_ge_one]) (by linarith [X.E_ge_one])
      hbarrier heff
  have hbudget := ReducedSourceShiftBudget.shift_and_loss_bounds N gq.1 gq.2 h (by omega) hg hq hscale hroot K A hK hA hshift
  have hh' : (h' : ℤ) ≠ 0 := by exact_mod_cast hbudget.1.ne'
  have hshortY : |((h' : ℤ) : ℝ)| ≤ K' * (Real.log N') ^ A := by
    simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg h' : (0 : ℝ) ≤ h')] using hbudget.2.1
  have hlossY : loss gq.1 gq.2 ≤ (2 * K') * (Real.log N') ^ A := by
    simpa only [K', mul_assoc] using hbudget.2.2.2
  have hsigned : SignedPopulation Y (h' : ℤ) (family gq S) := by
    refine ⟨hpop.d_bounds, hpop.e_bounds, hpop.u_bounds, hpop.v_bounds, ?_⟩
    intro r hr
    simpa only [Int.cast_natCast] using hpop.equation r hr
  have hcount := hL N' hNL (h' : ℤ) hh' hshortY Y dY (loss gq.1 gq.2) hbudget.2.2.1 hlossY
    hbarrierY (family gq S) hsigned hprim
  simpa only [hD, hE, hU, hV] using hcount

end PaperP1.ActualReducedFamilyCount
