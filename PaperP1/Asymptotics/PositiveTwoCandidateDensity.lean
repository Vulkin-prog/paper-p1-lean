module

public import PaperP1.Arithmetic.SlidingWindowDensity
public import PaperP1.Analysis.PolynomialSmoothDyadicDensity
public import PaperP1.Analysis.SaddleLogPrefactors
public import PaperP1.Arithmetic.OrdinarySmoothSourcePopulation
public import PaperP1.Asymptotics.ForcingExceptionLedger
public import PaperP1.Analysis.CoarseSaddlePowerErrors

/-! # A positive fraction of actual critical windows have two ordinary candidates

The internal dyadic smooth census and a finite incidence budget suffice for a
fixed positive fraction, with no almost-everywhere short-interval hypothesis.
This does not assert that the exceptional fraction tends to zero.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveTwoCandidateDensity

open Finset Filter SlidingWindowDensity OrdinarySmoothDyadicDensity OddPrimePivot
  NonanchorPivotSelection ForcingExceptionalSets OrdinarySmoothSourcePopulation

theorem uniform_two_candidates (C α : ℝ) (hα : 0 < α) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ, ∀ i : Fin 2,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        δ * (N : ℝ) ≤ ((boundaryBlock N).filter fun j ↦
          2 ≤ (ordinaryIndices j (L + i.val + 1) ((N : ℝ) ^ α)).card).card := by
  obtain ⟨δ, hδ, NF, hf⟩ := PolynomialSmoothDyadicDensity.uniform_lower α hα
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := 1 / Real.log 2 + |C| + 4
  obtain ⟨NW, hw⟩ := SaddleLogPrefactors.logarithmic_width_le_height (4 * D / δ)
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NG, hg⟩ := eventually_atTop.mp
    (hlogT.eventually (eventually_ge_atTop (max 1 ((C + 4 / δ) * Real.log 2))))
  refine ⟨δ / 2, by positivity, max NF (max NW NG), ?_⟩
  intro N hN L i hcrit
  let H := Real.log (N : ℝ)
  let B := L + i.val + 1
  let S := dyadicSmooth N ⌊(N : ℝ) ^ α⌋₊
  have hH := hg N (by omega)
  have hH1 : 1 ≤ H := (le_max_left _ _).trans hH
  have hHlarge : C + 4 / δ ≤ H / Real.log 2 :=
    (le_div_iff₀ hl2).mpr ((le_max_right _ _).trans hH)
  have hLlow := (abs_le.mp hcrit).1
  have hLhigh := (abs_le.mp hcrit).2
  change -C ≤ (L : ℝ) - H / Real.log 2 at hLlow
  change (L : ℝ) - H / Real.log 2 ≤ C at hLhigh
  have hi : (i.val : ℝ) ≤ 1 := by exact_mod_cast (show i.val ≤ 1 by omega)
  have hB : (B : ℝ) = (L : ℝ) + i.val + 1 := by simp only [B, Nat.cast_add, Nat.cast_one]
  have hlarge : 4 ≤ δ * (B : ℝ) := by
    have hh : 4 / δ ≤ (B : ℝ) := by linarith only [hLlow, hHlarge, hB, Nat.cast_nonneg (α := ℝ) i.val]
    have hx := (div_le_iff₀ hδ).mp hh
    nlinarith only [hx]
  have hshort : (B : ℝ) + 2 ≤ δ * N / 4 := by
    have hCmul : |C| + 4 ≤ (|C| + 4) * H := le_mul_of_one_le_right (by positivity) hH1
    have hupper : (B : ℝ) + 2 ≤ D * H := by
      have hid : D * H = H / Real.log 2 + (|C| + 4) * H := by dsimp only [D]; ring
      rw [hid]
      linarith only [hLhigh, hB, hi, hCmul, le_abs_self C]
    have hx : 4 * D * H / δ ≤ (N : ℝ) := by
      convert hw N (by omega) using 1
      ring
    have hpaid := (div_le_iff₀ hδ).mp hx
    exact hupper.trans (by nlinarith only [hpaid])
  have hS : S ⊆ Ico N (2 * N) := filter_subset _ _
  have hcount := SlidingWindowDensity.density_lower (S := S) (by omega : 2 ≤ N)
    (by dsimp only [B]; omega : 0 < B) hS δ (hf N (by omega)) hlarge hshort
  have hsub : goodWindows N B S ⊆ ((boundaryBlock N).filter fun j ↦
      2 ≤ (ordinaryIndices j B ((N : ℝ) ^ α)).card) := by
    intro j hj
    obtain ⟨hjN, hjcard⟩ := mem_filter.mp hj
    have hindices : selectedIndices j B S ⊆ ordinaryIndices j B ((N : ℝ) ^ α) := by
      intro o ho
      have hsn := (mem_filter.mp ho).2
      have hnat := (mem_filter.mp hsn).2
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      have hcast : (largestPrimeFactor (j + o.val) : ℝ) ≤ ⌊(N : ℝ) ^ α⌋₊ := by exact_mod_cast hnat
      exact hcast.trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) α))
    exact mem_filter.mpr ⟨hjN, hjcard.trans (card_le_card hindices)⟩
  have hc : ((goodWindows N B S).card : ℝ) ≤
      ((boundaryBlock N).filter fun j ↦ 2 ≤ (ordinaryIndices j B ((N : ℝ) ^ α)).card).card :=
    by exact_mod_cast card_le_card hsub
  exact hcount.trans hc

theorem uniform_clean_two_candidates (C D α : ℝ) (hD : 0 ≤ D) (hα : 0 < α) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ, ∀ i : Fin 2, ∀ B Z : ℕ,
      1 ≤ B → (B : ℝ) ≤ D * Real.log N → 1 ≤ Z → (Z : ℝ) ≤ Real.log N ^ 5 →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        δ * (N : ℝ) ≤ (goodSources N (L + i.val) B Z ((N : ℝ) ^ α)).card := by
  obtain ⟨δ, hδ, NC, hc⟩ := uniform_two_candidates C α hα
  obtain ⟨NE, he⟩ := ForcingExceptionLedger.uniform_exception_counts D hD (1 / 40) (by norm_num)
  obtain ⟨NP, hp⟩ := CoarseSaddlePowerErrors.power_negligible 1 (37 / 40) 0 (δ / 2)
    (by norm_num) (by positivity)
  refine ⟨δ / 2, by positivity, max NC (max NE NP), ?_⟩
  intro N hN L i B Z hB hwidth hZ hcut hcrit
  have hgood := hc N (by omega) L i hcrit
  have hbad := (he N (by omega) B Z (2 * N + B) 0 0 hB hwidth hZ hcut le_rfl (by omega) (by omega)).1
  norm_num only [show (9 : ℝ) / 10 + 1 / 40 = 37 / 40 by norm_num] at hbad
  have hpower := hp N (by omega)
  norm_num only [Real.rpow_one, neg_zero, zero_mul, Real.exp_zero, mul_one] at hpower
  have hbadsmall : ((badBoundaries N B Z).card : ℝ) ≤ δ / 2 * N := hbad.trans hpower
  let A := (boundaryBlock N).filter fun j ↦ 2 ≤ (ordinaryIndices j (L + i.val + 1) ((N : ℝ) ^ α)).card
  have hcover : A ⊆ goodSources N (L + i.val) B Z ((N : ℝ) ^ α) ∪ badBoundaries N B Z := by
    intro j hj
    obtain ⟨hjN, hjcount⟩ := mem_filter.mp hj
    by_cases hbadj : j ∈ badBoundaries N B Z
    · exact mem_union_right _ hbadj
    · exact mem_union_left _ (mem_goodSources.mpr ⟨hjN, hjcount, hbadj⟩)
  have hcard : (A.card : ℝ) ≤ (goodSources N (L + i.val) B Z ((N : ℝ) ^ α)).card +
      (badBoundaries N B Z).card := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le _ _)
  change δ * (N : ℝ) ≤ A.card at hgood
  nlinarith only [hgood, hcard, hbadsmall]

end PaperP1.PositiveTwoCandidateDensity
