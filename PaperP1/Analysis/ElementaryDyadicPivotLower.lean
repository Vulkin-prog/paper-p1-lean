module

public import PaperP1.Analysis.ElementaryReciprocalPrimeLower
public import PaperP1.Arithmetic.DyadicOddPivots
public import PaperP1.Analysis.BinaryLogarithmicBudget

/-! # Unconditional power-scale lower bounds on the literal dyadic pivot sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ElementaryDyadicPivotLower

open Finset PaperP1.OddPrimePivot PaperP1.ReciprocalOddPivots PaperP1.DyadicOddPivots
  DegreeUniformAffineParameters

theorem uniform_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, (N : ℝ) ^ (1 - ε) ≤ dyadicSum N := by
  let η := min (ε / 4) (1 / 8)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε / 4 := min_le_left _ _
  have hηsmall : η ≤ 1 / 8 := min_le_right _ _
  obtain ⟨NF, hNF, hf⟩ := ElementaryReciprocalPrimeLower.uniform_lower η hη
  obtain ⟨NS, hs⟩ := HalfCountSchedule.factor_absorption 8 (1 / 2) (3 / 8) (by norm_num)
  obtain ⟨NK, hNK, hk⟩ := BinaryLogarithmicBudget.polynomial_absorption 4 1 (ε - η) (by linarith only [hε, hηε])
  refine ⟨2 + NF + NS + NK, by omega, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let K : ℝ := ((Nat.clog 2 N + 1 : ℕ) : ℝ)
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hclog : Nat.clog 2 N ≤ logarithmicBudget N :=
    Nat.clog_le_of_le_pow (binary_upper N).le
  have hL1 : 1 ≤ logarithmicBudget N := by unfold logarithmicBudget; omega
  have hKbound : 2 * K ≤ 4 * (logarithmicBudget N : ℝ) := by
    have hh : Nat.clog 2 N + 1 ≤ 2 * logarithmicBudget N := by omega
    have hhR : K ≤ 2 * (logarithmicBudget N : ℝ) := by
      dsimp only [K]
      exact_mod_cast hh
    linarith only [hhR]
  have hKpower : 2 * K ≤ (N : ℝ) ^ (ε - η) := by
    have hh := hk N (by omega)
    simp only [pow_one, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * logarithmicBudget N)] at hh
    exact hKbound.trans hh
  have hroot : (Nat.sqrt N : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    have hs : (Nat.sqrt N : ℝ) ^ 2 ≤ (N : ℝ) ^ 1 := by
      simpa only [pow_one] using (show (Nat.sqrt N : ℝ) ^ 2 ≤ N by
        exact_mod_cast (Nat.le_sqrt'.mp (le_refl (Nat.sqrt N))))
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (HostRealPowers.le_rpow_div_of_pow_le (Nat.cast_nonneg (Nat.sqrt N)) hn.le (by decide : 0 < 2) hs)
  have hroot1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hsmall : 2 * (2 * ((Nat.sqrt N : ℝ) + 1)) ≤ (N : ℝ) ^ (1 - η) := by
    calc
      _ ≤ 8 * (N : ℝ) ^ (1 / 2 : ℝ) := by linarith only [hroot, hroot1]
      _ ≤ (N : ℝ) ^ ((1 / 2 : ℝ) + 3 / 8) := hs N (by omega)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hηsmall])
  have htarget : (2 * K) * (N : ℝ) ^ (1 - ε) ≤ (N : ℝ) ^ (1 - η) := by
    calc
      _ ≤ (N : ℝ) ^ (ε - η) * (N : ℝ) ^ (1 - ε) :=
        mul_le_mul_of_nonneg_right hKpower (by positivity)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  have hfinite : pivotSum N ≤ 2 * ((Nat.sqrt N : ℝ) + 1) + K * dyadicSum N := by
    simpa only [K, Nat.cast_add, Nat.cast_one] using full_dyadic_lower_transfer N (by omega)
  have hfull := hf N (by omega)
  have hmass : (2 * K) * (N : ℝ) ^ (1 - ε) ≤ (2 * K) * dyadicSum N := by
    nlinarith only [htarget, hfinite, hfull, hsmall]
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * K)).mp hmass

end PaperP1.ElementaryDyadicPivotLower
