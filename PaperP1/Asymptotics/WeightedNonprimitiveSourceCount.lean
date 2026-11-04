module

public import PaperP1.Asymptotics.WeightedOriginalScaleFamilyCount

/-! # Full nonprimitive signed source counts with a separately budgeted weakened barrier -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedNonprimitiveSourceCount

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantSourceBox
open PaperP1.IntegralSourceCoefficients PaperP1.ActualSourcePrimitiveReduction
open PaperP1.DeterminantPrimitiveReduction PaperP1.DeterminantLogScale PaperP1.DeterminantSignedBoxes

theorem uniform_positive_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (δ C ρ Kbar Abar K A ε : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hKbar : 0 ≤ Kbar) (hAbar : 0 ≤ Abar) (hK : 0 ≤ K) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℕ, 0 < h → (h : ℝ) ≤ K * (Real.log N) ^ A →
      ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X, ∀ Γ : ℝ, 0 ≤ Γ → Γ ≤ Kbar * (Real.log N) ^ Abar →
      (N : ℝ) ≤ Γ * X.c₁ * X.c₂ * (X.D * X.E) ^ 2 →
      ∀ S : Finset Quad, Population X h S →
      (S.card : ℝ) ≤ (N : ℝ) ^ ε *
        min (Real.sqrt (X.D * X.E * Real.exp (logShape N X.D X.E X.U X.V)) + X.D + X.E)
          (Real.sqrt (X.U * X.V * Real.exp (logShape N X.D X.E X.U X.V)) + X.U + X.V) := by
  classical
  obtain ⟨Nf, hf⟩ := WeightedOriginalScaleFamilyCount.uniform_count hHB hNG δ C ρ Kbar Abar K A (ε / 2)
    hδ hC hρ hρ₁ hKbar hAbar hK hA (by positivity)
  obtain ⟨Nh, hNh⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow K A (ε / 4) (by positivity)
  refine ⟨max 1 (max Nf Nh), ?_⟩
  intro N hN h hh hshift X coefs Γ hΓ hΓbudget hbarrier S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let F := Real.exp (logShape N X.D X.E X.U X.V)
  let cost := min (Real.sqrt (X.D * X.E * F) + X.D + X.E) (Real.sqrt (X.U * X.V * F) + X.U + X.V)
  have hcost : 0 ≤ cost := by
    have hd := X.D_ge_one
    have he := X.E_ge_one
    have hu := X.U_ge_one
    have hv := X.V_ge_one
    dsimp only [cost]
    apply le_min <;> positivity
  have hpow : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg hn.le _
  have hfamily : ∀ gq ∈ reductions h, ((family gq S).card : ℝ) ≤ (N : ℝ) ^ (ε / 2) * cost := by
    intro gq _hgq
    by_cases hne : (family gq S).Nonempty
    · exact hf N (by omega) h hh hshift X coefs Γ hΓ hΓbudget hbarrier S hS gq hne
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simpa only [card_empty, Nat.cast_zero] using mul_nonneg hpow hcost
  have hshort : (h : ℝ) ≤ (N : ℝ) ^ (ε / 4) := hshift.trans (hNh N (by omega))
  have hcard : ((reductions h).card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    have hcount : ((reductions h).card : ℝ) ≤ (h : ℝ) ^ 2 := by exact_mod_cast reductions_card h
    have hpower : (N : ℝ) ^ (ε / 2) = ((N : ℝ) ^ (ε / 4)) ^ 2 := by
      rw [show ε / 2 = (ε / 4) * 2 by ring, Real.rpow_mul hn.le, Real.rpow_two]
    rw [hpower]
    exact hcount.trans (pow_le_pow_left₀ (Nat.cast_nonneg h) hshort 2)
  have hcover : (S.card : ℝ) ≤ ∑ gq ∈ reductions h, ((family gq S).card : ℝ) := by
    exact_mod_cast finite_source_cover coefs hh S hS
  change (S.card : ℝ) ≤ (N : ℝ) ^ ε * cost
  calc
    _ ≤ ∑ gq ∈ reductions h, ((family gq S).card : ℝ) := hcover
    _ ≤ ∑ _gq ∈ reductions h, (N : ℝ) ^ (ε / 2) * cost := sum_le_sum hfamily
    _ = ((reductions h).card : ℝ) * ((N : ℝ) ^ (ε / 2) * cost) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * cost) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hpow hcost)
    _ = _ := by rw [← mul_assoc, ← Real.rpow_add hn]; congr 2; ring

theorem uniform_signed_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (δ C ρ Kbar Abar K A ε : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hKbar : 0 ≤ Kbar) (hAbar : 0 ≤ Abar) (hK : 0 ≤ K) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ K * (Real.log N) ^ A →
      ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X, ∀ Γ : ℝ, 0 ≤ Γ → Γ ≤ Kbar * (Real.log N) ^ Abar →
      (N : ℝ) ≤ Γ * X.c₁ * X.c₂ * (X.D * X.E) ^ 2 →
      ∀ S : Finset Quad, SignedPopulation X h S →
      (S.card : ℝ) ≤ (N : ℝ) ^ ε *
        min (Real.sqrt (X.D * X.E * Real.exp (logShape N X.D X.E X.U X.V)) + X.D + X.E)
          (Real.sqrt (X.U * X.V * Real.exp (logShape N X.D X.E X.U X.V)) + X.U + X.V) := by
  obtain ⟨N₀, hN₀⟩ := uniform_positive_count hHB hNG δ C ρ Kbar Abar K A ε hδ hC hρ hρ₁ hKbar hAbar hK hA hε
  refine ⟨N₀, ?_⟩
  intro N hN h hh hshift X coefs Γ hΓ hΓbudget hbarrier S hS
  have hnat : 0 < h.natAbs := Int.natAbs_pos.mpr hh
  have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hbarrier' : (N : ℝ) ≤ Γ * (DeterminantPositiveOrientation.orientedBox h X).c₁ *
      (DeterminantPositiveOrientation.orientedBox h X).c₂ *
      ((DeterminantPositiveOrientation.orientedBox h X).D * (DeterminantPositiveOrientation.orientedBox h X).E) ^ 2 := by
    have heq := congrArg (fun B : ℝ ↦ Γ * B) (barrier_orientation h X)
    have hbase : (N : ℝ) ≤ Γ * (X.c₁ * X.c₂ * (X.D * X.E) ^ 2) := by simpa only [mul_assoc] using hbarrier
    rw [← heq] at hbase
    simpa only [mul_assoc] using hbase
  have hc := hN₀ N hN h.natAbs hnat (by simpa only [habs] using hshift)
    (DeterminantPositiveOrientation.orientedBox h X) (oriented h coefs) Γ hΓ hΓbudget hbarrier'
    (DeterminantPositiveOrientation.orientedPopulation h S) (DeterminantPositiveOrientation.population X h S hS)
  simpa only [DeterminantPositiveOrientation.card_eq, DeterminantPositiveOrientation.shape_eq,
    DeterminantPositiveOrientation.horizontal_cost_eq, DeterminantPositiveOrientation.vertical_cost_eq] using hc

end PaperP1.WeightedNonprimitiveSourceCount
