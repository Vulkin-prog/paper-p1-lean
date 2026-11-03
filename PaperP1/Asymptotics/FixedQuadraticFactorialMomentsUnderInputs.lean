module

public import PaperP1.Asymptotics.FullFixedActivityUnderInputs
public import PaperP1.Asymptotics.SubpowerPairAbsoluteActivity
public import PaperP1.Asymptotics.ActualPairRowActivity
public import PaperP1.Algebra.QuadraticMomentApproximation
public import PaperP1.Model.HeterogeneousRunConversion

/-! # Every actual fixed factorial moment has its exact quadratic correction with remainder exponent1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedQuadraticFactorialMomentsUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CoarseConnectedParameters
  PaperP1.FactorialCountMoments PaperP1.HeterogeneousDirectMaximum

theorem uniform_fixed (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ pc pi pd : Parameters r, ∃ pp pq : FinitePairDeficitInputs.Parameters,
      Hypotheses pc (ε / 128) → Hypotheses pi (ε / 512) →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 524288)) →
      Hypotheses pd (min (ε / 32) (1 / 12) / 8) →
      FinitePairDeficitInputs.Hypotheses pq (GeneralGraphHostCount.sizeCap (min (ε / 32) (1 / 12) / 8192)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        |factorialCountMoment G L r - actualMean G L ^ r -
          (r.choose 2 : ℝ) * actualMean G L ^ (r - 2) * RegularCumulantTransfer.secondFactorialCumulant G L| ≤
            (N : ℝ) ^ (-1 + ε) := by
  classical
  let M := max 1 (2 * (2 : ℝ) ^ C)
  have hM : 1 ≤ M := le_max_left _ _
  have hMzero : 0 ≤ M := by linarith only [hM]
  let K₀ := (r : ℝ) ^ 2 * M ^ r
  let K₁ := (((r - 2 : ℕ) : ℝ) ^ 2 + 2 * (r - 2 : ℕ)) * M ^ (r - 2)
  let K₂ := M ^ r * ((r + 1 : ℕ) : ℝ)
  let K₃ := (r.choose 2 : ℝ) * M ^ (r + 1)
  let D := (r.factorial : ℝ) * (K₀ * M + K₁ * M + K₂) + K₃ * M
  obtain ⟨pc, pi, pd, pp, pq, ha⟩ := FullFixedActivityUnderInputs.uniform_range r C (ε / 4) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := SubpowerPairAbsoluteActivity.uniform_bound C (ε / 4) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NC, _hNC, hc⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption D (-1 + ε / 4) (3 * ε / 4) (by positivity)
  refine ⟨pc, pi, pd, pp, pq, ?_⟩
  intro hgeoC hgeoI hgeoP hgeoD hgeoQ
  have hsC : (ε / 4) / 32 = ε / 128 := by ring
  have hsI : (ε / 4) / 128 = ε / 512 := by ring
  have hsP : (ε / 4) / 131072 = ε / 524288 := by ring
  have hsD : (ε / 4) / 8 = ε / 32 := by ring
  obtain ⟨NA, _hNA, ha⟩ := ha (by simpa only [hsC] using hgeoC)
    (by simpa only [hsI] using hgeoI) (by simpa only [hsP] using hgeoP)
    (by simpa only [hsD] using hgeoD) (by simpa only [hsD] using hgeoQ)
  refine ⟨10 + NP + NM + NC + NF + NA, by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let κ := M / N
  let T := (N : ℝ) ^ (-1 + ε / 4)
  let A₂ := ∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e|
  let W := ∑ s ∈ Icc 3 r, ∑ I ∈ G.powersetCard s, |infiniteCenteredCoefficient L I|
  have hκ : 0 ≤ κ := div_nonneg hMzero hn.le
  have hT : 0 ≤ T := Real.rpow_nonneg hn.le _
  have hmean : (∑ x ∈ G, infiniteMarginal x L) ≤ M := by
    calc
      _ ≤ actualMean (dyadicBlock N) L := sum_le_sum_of_subset_of_nonneg hG
        (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = CountObservables.countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment Subset.rfl
      _ ≤ 2 * (2 : ℝ) ^ C := (hm N (by omega) L hband).2
      _ ≤ _ := le_max_right _ _
  have hcap (x : ℕ) (hx : x ∈ G) : infiniteMarginal x L ≤ κ :=
    (hc N (by omega) L hband x (hG hx)).trans
      (div_le_div_of_nonneg_right (le_max_right 1 (2 * (2 : ℝ) ^ C)) hn.le)
  have hW : W ≤ ((r + 1 : ℕ) : ℝ) * T := by
    calc
      _ ≤ ∑ _s ∈ Icc 3 r, T := sum_le_sum fun s hs ↦
        ha N (by omega) L hband s (mem_Icc.mp hs).1 (mem_Icc.mp hs).2 G hG
      _ = ((Icc 3 r).card : ℝ) * T := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (show (Icc 3 r).card ≤ r + 1 by rw [Nat.card_Icc]; omega)) hT
  have hpair : A₂ ≤ (N : ℝ) ^ (ε / 4) := hp N (by omega) L hband G hG
  have hκT : κ ≤ M * T := by
    have heq : κ = M * (N : ℝ) ^ (-1 : ℝ) := by dsimp only [κ]; rw [Real.rpow_neg_one, div_eq_mul_inv]
    rw [heq]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])) hMzero
  have hκpair : κ * A₂ ≤ M * T := by
    calc
      _ ≤ κ * (N : ℝ) ^ (ε / 4) := mul_le_mul_of_nonneg_left hpair hκ
      _ = M * T := by dsimp only [κ, T]; rw [div_eq_mul_inv, ← Real.rpow_neg_one, mul_assoc, ← Real.rpow_add hn]
  have hfinite := QuadraticMomentApproximation.factorial_error_bound G (fun x ↦ infiniteMarginal x L)
    (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    (infiniteJointMoment L) (infiniteCenteredCoefficient L)
    (fun I _ ↦ CompressedJointMoments.infinite_uncentered_expansion L I)
    (CompressedJointMoments.centered_empty L) (ActualCanonicalComponents.singleton_zero L)
    r hr κ M hκ hM hcap hmean
  have hsecond := HeterogeneousRunConversion.second_cumulant_formula (L := L) hG
  change RegularCumulantTransfer.secondFactorialCumulant G L =
    2 * (∑ e ∈ G.powersetCard 2, infiniteCenteredCoefficient L e) - ∑ x ∈ G, infiniteMarginal x L ^ 2 at hsecond
  rw [← factorialCountMoment_eq_subset hG r, ← hsecond] at hfinite
  have hfinite' : |factorialCountMoment G L r - actualMean G L ^ r -
      (r.choose 2 : ℝ) * actualMean G L ^ (r - 2) * RegularCumulantTransfer.secondFactorialCumulant G L| ≤
      (r.factorial : ℝ) * (K₀ * κ + K₁ * (κ * A₂) + M ^ r * W) + K₃ * κ := by
    simpa only [K₀, K₁, K₃, A₂, W, actualMean, mul_assoc, mul_left_comm, mul_comm] using hfinite
  calc
    _ ≤ (r.factorial : ℝ) * (K₀ * κ + K₁ * (κ * A₂) + M ^ r * W) + K₃ * κ := hfinite'
    _ ≤ (r.factorial : ℝ) * (K₀ * (M * T) + K₁ * (M * T) + M ^ r * (((r + 1 : ℕ) : ℝ) * T)) + K₃ * (M * T) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hκT (by dsimp [K₀]; positivity))
          (mul_le_mul_of_nonneg_left hκpair (by dsimp [K₁]; positivity)))
          (mul_le_mul_of_nonneg_left hW (pow_nonneg hMzero _))
      · exact mul_le_mul_of_nonneg_left hκT (by dsimp [K₃]; positivity)
    _ = D * T := by dsimp only [D, K₂]; ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 4) + 3 * ε / 4) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.FixedQuadraticFactorialMomentsUnderInputs
