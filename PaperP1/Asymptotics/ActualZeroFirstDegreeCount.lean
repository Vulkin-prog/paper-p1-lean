module

public import PaperP1.Arithmetic.ActualSourceArithmetic
public import PaperP1.Asymptotics.SourceFactorPreimages
public import PaperP1.Asymptotics.UniformLinearFactorDegrees

/-! # Unconditional numerical counts on the actual first-degree-zero factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualZeroFirstDegreeCount

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantIntervalPartition
open PaperP1.ActualProjectivePairs PaperP1.BivariateDegrees PaperP1.IntegerPairFactorCover
open PaperP1.ConstructedClusterCurveData PaperP1.IntegralSourceCoefficients PaperP1.SourceFactorPreimages

theorem uniform_sourcePart_count (Bmax : ℕ) (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ δ : ℝ, ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ N ^ 2 → ∀ Q : Finset Quad, SignedPopulation X h Q →
      (∀ p ∈ Q, Primitive p) → ∀ B A D : Matrix (Fin 2) (Fin 2) ℤ,
      A * D = 1 → D * A = 1 → ∀ c : Bool × Bool, ∀ G : ℤ[X][X], G ≠ 0 →
      degreeX G = 0 → degreeY G ≤ Bmax → (sourcePart G B D c Q).card ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nh, _, hh⟩ := ActualSourceArithmetic.uniform_polynomial_height C hC
  choose Nd hNd using fun j : Fin (Bmax + 1) ↦ ZeroDegreeQuadraticFibres.auxiliary_zero_count j.val 2 ε hε
  refine ⟨max Nh (univ.sup Nd), ?_⟩
  intro N hN ρ δ X coefs h hzero hshift Q hQ hprim B A D hAD hDA c G hG hfirst hsecond
  obtain ⟨hc₁, hc₂, hheight⟩ := hh N (by omega) ρ δ X coefs h Q hQ
  let j : Fin (Bmax + 1) := ⟨degreeY G, by omega⟩
  have hNj : Nd j ≤ N := (le_sup (f := Nd) (mem_univ j)).trans (le_max_right _ _ |>.trans hN)
  let Q' := sourcePart G B D c Q
  have hpop : SignedPopulation X h Q' := sourcePart_population hQ G B D c
  have hcard : (Q'.image integerPoint).card = Q'.card := card_image_of_injective _ integerPoint_injective
  rw [← hcard]
  apply hNd j N hNj coefs.c₁ coefs.c₂ (N ^ 2) h (by have := (positive coefs).1; omega)
    (by have := (positive coefs).2; omega) hzero hc₁ hc₂ le_rfl hshift
    (pullSecondForm G D c.2) (pullSecondForm_homogeneous G D c.2)
    (pullSecondForm_nonzero G hG hfirst A D hAD hDA c.2)
  · intro s hs
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hs
    have hpQ := sourcePart_subset G B D c Q hp
    exact ActualSourceArithmetic.quadratic_valid coefs hpop p hp (hprim p hpQ) (hheight p hpQ)
  · intro s hs
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hs
    exact sourcePart_second_form_zero G hfirst B D c Q p hp

theorem uniform_actual_count (Bmax : ℕ) (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ δ : ℝ, ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      ∀ κ₀ κ₁ κf Amax M k : ℕ, ∀ A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ,
      ∀ L₀ L₁ T₀ T₁ : ℝ,
      HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁ →
      VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁ →
      ∀ h : ℤ, h ≠ 0 → h.natAbs ≤ N ^ 2 → ∀ S : Finset Quad, SignedPopulation X h S →
      (∀ p ∈ S, Primitive p) → ∀ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax Bmax (cluster M X.D X.E k S) B₀ B₁ L₀ T₀ F →
      ∀ c : Bool × Bool, ∀ G ∈ F c, degreeX G = 0 →
        ((zeros G (FourProjectiveCharts.population c
          ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := uniform_sourcePart_count Bmax C hC ε hε
  refine ⟨N₀, ?_⟩
  intro N hN ρ δ X coefs κ₀ κ₁ κf Amax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ _hD hU h hh hshift S hS hprim F hcover c G hG hfirst
  have hfactor := (hcover.factors c).2.1 G hG
  have hcount := hN₀ N hN ρ δ X coefs h hh hshift (cluster M X.D X.E k S)
    (ActualFirstLinearFactorCount.cluster_population hS M k)
    (fun p hp ↦ hprim p ((mem_cluster _ _ _ _ _ _).mp hp).1)
    B₀ A₁ B₁ hU.right_inverse hU.left_inverse c G hfactor.1.ne_zero hfirst hfactor.2.2.2.1
  have hcard := factor_population_card_le_sourcePart G B₀ B₁ c (cluster M X.D X.E k S)
    (fun p hp ↦ ⟨(hcover.chart_points c p hp).2.2.1, (hcover.chart_points c p hp).2.2.2.1⟩)
  exact (by exact_mod_cast hcard : (_ : ℝ) ≤ _).trans hcount

theorem uniform_normalized_actual_count (Bmax : ℕ) (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ δ : ℝ, ∀ X : Box N ρ C δ, ∀ _coefs : IntegerCoefficients X,
      ∀ κ₀ κ₁ κf Amax M k : ℕ, ∀ A₀ B₀ A₁ B₁ : Matrix (Fin 2) (Fin 2) ℤ,
      ∀ L₀ L₁ T₀ T₁ : ℝ,
      HorizontalGridCoordinateData.Data X κ₀ M k A₀ B₀ L₀ L₁ →
      VerticalGridCoordinateData.Data X κ₁ M (QuadraticIntervalGrid.grid M k) A₁ B₁ T₀ T₁ →
      1 ≤ M → ∀ h : ℤ, h ≠ 0 → (M : ℝ) * |(h : ℝ)| ≤ N → ∀ S : Finset Quad, SignedPopulation X h S →
      (∀ p ∈ S, Primitive p) → ∀ F : Bool × Bool → Finset ℤ[X][X],
      LocalCover N κf Amax Bmax (cluster M X.D X.E k S) B₀ B₁ L₀ T₀ F →
      ∀ c : Bool × Bool, ∀ G ∈ F c, degreeX G = 0 →
        ((zeros G (FourProjectiveCharts.population c
          ((cluster M X.D X.E k S).image (coordinates B₀ B₁)))).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := uniform_actual_count Bmax C hC ε hε
  refine ⟨max 1 N₀, ?_⟩
  intro N hN ρ δ X coefs κ₀ κ₁ κf Amax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁ hD hU hM h hh hMh S hS hprim F hcover c G hG hfirst
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hAbsR : |(h : ℝ)| ≤ N := by
    have hm := mul_le_mul_of_nonneg_right hMR (abs_nonneg (h : ℝ))
    nlinarith only [hm, hMh]
  have hAbs : h.natAbs ≤ N := by
    exact_mod_cast (show (h.natAbs : ℝ) ≤ N by simpa only [Nat.cast_natAbs, Int.cast_abs] using hAbsR)
  have hshift : h.natAbs ≤ N ^ 2 := hAbs.trans (by nlinarith : N ≤ N ^ 2)
  exact hN₀ N (by omega) ρ δ X coefs κ₀ κ₁ κf Amax M k A₀ B₀ A₁ B₁ L₀ L₁ T₀ T₁
    hD hU h hh hshift S hS hprim F hcover c G hG hfirst

end PaperP1.ActualZeroFirstDegreeCount
