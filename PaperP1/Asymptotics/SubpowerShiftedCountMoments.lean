module

public import PaperP1.Model.ShiftedCountMoments
public import PaperP1.Asymptotics.SubpowerFixedCountMoments

/-! # Fixed moments of the actual positive envelope Z+mu are subpolynomial without BCN -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubpowerShiftedCountMoments

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HeterogeneousDirectMaximum

theorem uniform_bound (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ShiftedCountMoments.moment G L r ≤ (N : ℝ) ^ ε := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let M := 2 * (2 : ℝ) ^ C
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨NZ, _hNZ, hz⟩ := SubpowerFixedCountMoments.uniform_ordinary r C δ hδ
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 ^ r * (1 + M ^ r)) δ δ hδ
  refine ⟨max 2 (max NZ (max NM NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hmean0 : 0 ≤ actualMean G L := sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hmean : actualMean G L ≤ M := by
    calc
      _ ≤ actualMean (dyadicBlock N) L := sum_le_sum_of_subset_of_nonneg hG
        (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = CountObservables.countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment (subset_refl _)
      _ ≤ _ := (hm N (by omega) L hband).2
  have hpower := pow_le_pow_left₀ hmean0 hmean r
  have hlarge : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hn1 hδ.le
  have hstatic : M ^ r ≤ M ^ r * (N : ℝ) ^ δ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlarge (pow_nonneg hM r)
  calc
    _ ≤ 2 ^ r * (CountObservables.countMoment G L r + actualMean G L ^ r) := ShiftedCountMoments.finite_upper hG r
    _ ≤ (2 ^ r * (1 + M ^ r)) * (N : ℝ) ^ δ := by
      have hZ := hz N (by omega) L hband G hG
      have hinside := add_le_add hZ (hpower.trans hstatic)
      have hmul := mul_le_mul_of_nonneg_left hinside (by positivity : (0 : ℝ) ≤ 2 ^ r)
      nlinarith only [hmul]
    _ ≤ (N : ℝ) ^ (δ + δ) := hf N (by omega)
    _ = _ := by congr 1; dsimp [δ]; ring

end PaperP1.SubpowerShiftedCountMoments
