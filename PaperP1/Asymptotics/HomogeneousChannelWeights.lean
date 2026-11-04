module

public import PaperP1.Model.PairLossWeights
public import PaperP1.Model.HomogeneousSourcePairMass
public import PaperP1.Model.UnitFourierWeight
public import PaperP1.Asymptotics.AlignedPairRank
public import PaperP1.Asymptotics.PrivateChannelActivityRate
public import PaperP1.Asymptotics.WeakPairActivity
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # Every actual fixed-channel pair has its expected individual weight, even when nonprivate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousChannelWeights

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FixedChannelSourceGeometry PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss

theorem uniform_pair (C ε : ℝ) (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ xy ∈ unitSources N a b L,
      HomogeneousRunMass.probability L {xy.1, xy.2} ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let K : ℝ := ((2 : ℝ) ^ C) ^ 2 * (2 : ℝ) ^ ((C + 1) / b) * (2 : ℝ) ^ (η * (C + 1))
  obtain ⟨NR, hr⟩ := AlignedPairRank.units_residual_bound C η hη
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (max b 2)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K (-2 + 1 / (b : ℝ) + η) η hη
  refine ⟨max 2 (max NR (max NG NF)), by omega, ?_⟩
  intro N hN L hband xy hxy
  obtain ⟨hxyN, hu⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hxyN
  have hgeom := hg N (by omega) L hband
  have hxpos : 0 < xy.1 := by have h := (mem_Ico.mp hx).1; omega
  have hypos : 0 < xy.2 := by have h := (mem_Ico.mp hy).1; omega
  have hheight : b ≤ (L + 1) ^ 3 := (by omega : b ≤ L + 1).trans
    (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0))
  have hloss := hr N (by omega) L a b xy.1 xy.2 hband ha hab.le hheight hx hy hu
  have hunit := UnitFourierWeight.unit_kernel_rank_bound (L := L) ha (ha.trans hab) hcop hxpos hypos
  have hpower : (2 ^ pairLoss xy.1 xy.2 L : ℝ) ≤
      (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) * (2 : ℝ) ^ (η * ((L + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hloss, hunit])
  have hsmall : (2 : ℝ) ^ (η * ((L + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (η * (C + 1)) * (N : ℝ) ^ η := by
    have h := WeakPairActivityAsymptotic.critical_binary_power (by omega) hband η hη.le
    have heq : η * ((L + 1 : ℕ) : ℝ) = η * L + η := by push_cast; ring
    rw [heq, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ ((2 : ℝ) ^ (η * C) * (N : ℝ) ^ η) * (2 : ℝ) ^ η :=
        mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (by norm_num) _)
      _ = _ := by rw [show η * (C + 1) = η * C + η by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; ring
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairLoss xy.1 xy.2 L : ℝ) := (HomogeneousSourcePairMass.probability_pair hxpos hypos).le
    _ ≤ (((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 : ℝ)) *
        ((2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) * (2 : ℝ) ^ (η * ((L + 1 : ℕ) : ℝ))) :=
      mul_le_mul (CriticalChannelPowers.nominal_square_upper (by omega) hband) hpower (by positivity) (by positivity)
    _ ≤ (((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 : ℝ)) *
        (((2 : ℝ) ^ ((C + 1) / b) * (N : ℝ) ^ (1 / (b : ℝ))) *
          ((2 : ℝ) ^ (η * (C + 1)) * (N : ℝ) ^ η)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (CriticalChannelPowers.window_root_upper (by omega) (ha.trans hab) hband)
        hsmall (by positivity) (by positivity)) (by positivity)
    _ = K * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + η) := by
      rw [Real.rpow_add hn (-2 + 1 / (b : ℝ)) η, Real.rpow_add hn (-2) (1 / (b : ℝ))]
      dsimp [K]
      ring
    _ ≤ (N : ℝ) ^ ((-2 + 1 / (b : ℝ) + η) + η) := hf N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem regular_singleton {N L z : ℕ} (hz : z ∈ RegularStarts.regularStarts N L) :
    HomogeneousRunMass.probability L {z} = (2 ^ L : ℝ)⁻¹ := by
  rw [HomogeneousRunMass.regular_weight (singleton_subset_iff.mpr hz),
    HomogeneousRunMass.nominal_singleton]

end PaperP1.HomogeneousChannelWeights
