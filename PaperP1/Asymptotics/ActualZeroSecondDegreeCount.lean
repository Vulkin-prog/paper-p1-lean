module

public import PaperP1.Arithmetic.SourceLinearFibreBounds
public import PaperP1.Asymptotics.SourceFactorPreimages
public import PaperP1.Asymptotics.UniformLinearFactorDegrees

/-! # The actual second-degree-zero factors have the source-barrier linear-fibre bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualZeroSecondDegreeCount

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantIntervalPartition
open PaperP1.ActualProjectivePairs PaperP1.BivariateDegrees PaperP1.IntegerPairFactorCover
open PaperP1.ConstructedClusterCurveData PaperP1.IntegralSourceCoefficients PaperP1.SourceFactorPreimages

theorem sourcePart_count {N : ℕ} {ρ C δ : ℝ} (hC : 0 ≤ C) (X : Box N ρ C δ)
    (coefs : IntegerCoefficients X) (h : ℤ) (hh : h ≠ 0) (Q : Finset Quad) (hQ : SignedPopulation X h Q)
    (hprim : ∀ p ∈ Q, Primitive p) (A B D : Matrix (Fin 2) (Fin 2) ℤ)
    (hAB : A * B = 1) (hBA : B * A = 1) (c : Bool × Bool) (G : ℤ[X][X]) (hG : G ≠ 0)
    (hsecond : degreeY G = 0) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hbarrier : (N : ℝ) ≤ Γ * X.c₁ * X.c₂ * (X.D * X.E) ^ 2) :
    ((sourcePart G B D c Q).card : ℝ) ≤ 2 * (degreeX G + 1) * (Γ * (8 * C) * h.natAbs + 1) := by
  let Q' := sourcePart G B D c Q
  have hpop : SignedPopulation X h Q' := sourcePart_population hQ G B D c
  have hswap : Bivariate.swap G ≠ 0 := by
    intro hz
    apply hG
    exact (Bivariate.swap (R := ℤ)).injective (hz.trans (map_zero _).symm)
  have hfirst : degreeX (Bivariate.swap G) = 0 := by
    simpa only [BivariateProjectiveSwap.degreeX_swap] using hsecond
  have hform := pullSecondForm_homogeneous (Bivariate.swap G) B c.1
  have hform0 := pullSecondForm_nonzero (Bivariate.swap G) hswap hfirst A B hAB hBA c.1
  have hcount := ZeroDegreeLinearFibres.auxiliary_zero_count (degreeX G) coefs.c₁ coefs.c₂
    (by have := (positive coefs).1; omega) (by have := (positive coefs).2; omega) h hh N Γ (8 * C)
    (Nat.cast_nonneg N) hΓ (by positivity) (pullSecondForm (Bivariate.swap G) B c.1)
    (by simpa only [BivariateProjectiveSwap.degreeY_swap] using hform) hform0 (Q'.image integerPoint)
  have hb : ((Q'.image integerPoint).card : ℝ) ≤
      2 * (degreeX G + 1) * (Γ * (8 * C) * h.natAbs + 1) := by
    apply hcount
    · intro s hs
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hs
      exact ActualSourceArithmetic.linear_valid coefs hpop p hp (hprim p (sourcePart_subset G B D c Q hp))
    · intro s hs
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hs
      exact sourcePart_first_form_zero G hsecond B D c Q p hp
    · intro s hs
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hs
      exact SourceLinearFibreBounds.weighted_height coefs hpop p hp
    · intro s hs
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hs
      exact SourceLinearFibreBounds.coefficient_product coefs hpop Γ hΓ hbarrier p hp
  simpa only [card_image_of_injective Q' integerPoint_injective] using hb

theorem actual_count {N : ℕ} {ρ C δ : ℝ} (hC : 0 ≤ C) (X : Box N ρ C δ)
    (coefs : IntegerCoefficients X) (κ₀ κ₁ κf Amax Bmax M k : ℕ)
    (A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ) (L₀ L₁ T₀ T₁ : ℝ)
    (hD : HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁)
    (_hU : VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁)
    (h : ℤ) (hh : h ≠ 0) (S : Finset Quad) (hS : SignedPopulation X h S) (hprim : ∀ p ∈ S, Primitive p)
    (F : Bool × Bool → Finset ℤ[X][X])
    (hcover : LocalCover N κf Amax Bmax (cluster M X.D X.E k S) B₀ B₁ L₀ T₀ F)
    (c : Bool × Bool) (G : ℤ[X][X]) (hG : G ∈ F c) (hsecond : degreeY G = 0)
    (Γ : ℝ) (hΓ : 0 ≤ Γ) (hbarrier : (N : ℝ) ≤ Γ * X.c₁ * X.c₂ * (X.D * X.E) ^ 2) :
    ((zeros G (FourProjectiveCharts.population c
      ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤
      2 * (Amax + 1) * (Γ * (8 * C) * h.natAbs + 1) := by
  have hfactor := (hcover.factors c).2.1 G hG
  have hcount := sourcePart_count hC X coefs h hh (cluster M X.D X.E k S)
    (ActualFirstLinearFactorCount.cluster_population hS M k)
    (fun p hp ↦ hprim p ((mem_cluster _ _ _ _ _ _).mp hp).1)
    A₀ B₀ B₁ hD.right_inverse hD.left_inverse c G hfactor.1.ne_zero hsecond Γ hΓ hbarrier
  have hcard := factor_population_card_le_sourcePart G B₀ B₁ c (cluster M X.D X.E k S)
    (fun p hp ↦ ⟨(hcover.chart_points c p hp).2.2.1, (hcover.chart_points c p hp).2.2.2.1⟩)
  have hnat : (degreeX G : ℝ) ≤ Amax := by exact_mod_cast hfactor.2.2.1
  exact (show (_ : ℝ) ≤ _ by exact_mod_cast hcard).trans
    (hcount.trans (by gcongr))

end PaperP1.ActualZeroSecondDegreeCount
