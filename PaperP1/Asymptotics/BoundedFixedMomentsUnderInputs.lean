module

public import PaperP1.Asymptotics.FixedMomentInputs
public import PaperP1.Asymptotics.FinitePairActivityInputs
public import PaperP1.Model.TouchardCountMoments

/-! # Uniformly bounded actual fixed factorial and ordinary count moments under the existing finite geometric properties -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedFixedMomentsUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.CountObservables PaperP1.HeterogeneousDirectMaximum

theorem uniform_factorial (r : ℕ) (hr : 2 ≤ r) (C : ℝ) :
    ∃ p : FixedMomentInputs.Parameters r, ∃ pa : FinitePairDeficitInputs.Parameters,
      FixedMomentInputs.Hypotheses p (1 / 2) →
      FinitePairDeficitInputs.Hypotheses pa (GeneralGraphHostCount.sizeCap (1 / 100)) →
      ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        factorialCountMoment G L r ≤ B := by
  let M := max 1 (2 * (2 : ℝ) ^ C)
  let B := M ^ r + (r.choose 2 : ℝ) * M ^ (r - 2) + 1
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  obtain ⟨p, hp⟩ := FixedMomentInputs.uniform_fixed r hr C (1 / 2) (by norm_num)
  obtain ⟨pa, ha⟩ := FinitePairActivityInputs.uniform_cumulant C (1 / 6) (by norm_num)
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  refine ⟨p, pa, ?_⟩
  intro hgeo hgeoA
  obtain ⟨NF, _hNF, hf⟩ := hp hgeo
  obtain ⟨NA, _hNA, ha⟩ := ha hgeoA
  refine ⟨B, by dsimp [B]; positivity, 10 + NM + NF + NA, by omega, ?_⟩
  intro N hN L hband G hG
  let μ := actualMean G L
  let a := RegularCumulantTransfer.secondFactorialCumulant G L
  have hμ : 0 ≤ μ := sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hμM : μ ≤ M := by
    calc
      _ ≤ actualMean (dyadicBlock N) L := sum_le_sum_of_subset_of_nonneg hG
        (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment Subset.rfl
      _ ≤ 2 * (2 : ℝ) ^ C := (hm N (by omega) L hband).2
      _ ≤ _ := le_max_right _ _
  have hpower : (N : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  have haone : |a| ≤ 1 := by
    have h := ha N (by omega) L hband G hG
    norm_num only [show (-2 / 3 : ℝ) + 1 / 6 = -1 / 2 by ring] at h
    exact h.trans (by simpa only [neg_div] using hpower)
  have herror : |factorialCountMoment G L r - μ ^ r - (r.choose 2 : ℝ) * μ ^ (r - 2) * a| ≤ 1 := by
    have h := hf N (by omega) L hband G hG
    norm_num only [show (-1 : ℝ) + 1 / 2 = -1 / 2 by ring] at h
    exact h.trans (by simpa only [neg_div] using hpower)
  have hterm : (r.choose 2 : ℝ) * μ ^ (r - 2) * a ≤ (r.choose 2 : ℝ) * M ^ (r - 2) := by
    calc
      _ ≤ (r.choose 2 : ℝ) * μ ^ (r - 2) * 1 := mul_le_mul_of_nonneg_left
        ((le_abs_self a).trans haone) (by positivity)
      _ ≤ _ := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hμ hμM (r - 2)) (Nat.cast_nonneg _)
  have hμpow := pow_le_pow_left₀ hμ hμM r
  have hupper := (abs_le.mp herror).2
  dsimp only [B]
  linarith only [hupper, hterm, hμpow]

theorem uniform_ordinary (r : ℕ) (hr : 2 ≤ r) (C : ℝ) :
    ∃ p : FixedMomentInputs.Parameters r, ∃ pa : FinitePairDeficitInputs.Parameters,
      FixedMomentInputs.Hypotheses p (1 / 2) →
      FinitePairDeficitInputs.Hypotheses pa (GeneralGraphHostCount.sizeCap (1 / 100)) →
      ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        countMoment G L r ≤ B := by
  obtain ⟨p, pa, hp⟩ := uniform_factorial r hr C
  refine ⟨p, pa, ?_⟩
  intro hgeo hgeoA
  obtain ⟨B, hB, N₀, hN₀, hb⟩ := hp hgeo hgeoA
  refine ⟨(((2 * r) ^ r : ℕ) : ℝ) + 2 ^ r * B, by positivity, N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  exact (DependentFactorialBound.ordinary_upper hG r).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hb N hN L hband G hG) (by positivity)))

theorem uniform_low (r : ℕ) (hr : r ≤ 1) (C : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      countMoment G L r ≤ B := by
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  refine ⟨max 1 (2 * (2 : ℝ) ^ C), by positivity, 10 + NM, by omega, ?_⟩
  intro N hN L hband G hG
  have hcases : r = 0 ∨ r = 1 := by omega
  rcases hcases with rfl | rfl
  · rw [TouchardCountMoments.count_zero hG]
    exact le_max_left _ _
  · exact ((CriticalActualMean.mean_mono hG Subset.rfl).trans (hm N (by omega) L hband).2).trans
      (le_max_right _ _)

end PaperP1.BoundedFixedMomentsUnderInputs
