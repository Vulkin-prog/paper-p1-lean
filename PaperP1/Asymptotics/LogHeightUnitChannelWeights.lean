module

public import PaperP1.Model.PairLossWeights
public import PaperP1.Model.UnitFourierWeight
public import PaperP1.Asymptotics.AlignedPairRank
public import PaperP1.Asymptotics.PrivateChannelActivityRate
public import PaperP1.Asymptotics.WeakPairActivity
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # Uniform actual pair weights in all reduced exact-unit channels of height at most (L+1)^3 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogHeightUnitChannelWeights

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FixedChannelSourceGeometry PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss

theorem uniform_joint (b₀ : ℕ) (hb₀ : 0 < b₀) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ a b : ℕ,
      0 < a → a < b → a.Coprime b → b₀ ≤ b → b ≤ (L + 1) ^ 3 →
      ∀ xy ∈ unitSources N a b L,
      infiniteJointMoment L {xy.1, xy.2} ≤ (N : ℝ) ^ (-2 + 1 / (b₀ : ℝ) + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let K : ℝ := ((2 : ℝ) ^ C) ^ 2 * (2 : ℝ) ^ ((C + 1) / b₀) * (2 : ℝ) ^ (η * (C + 1))
  obtain ⟨NR, hr⟩ := AlignedPairRank.units_residual_bound C η hη
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K (-2 + 1 / (b₀ : ℝ) + η) η hη
  refine ⟨max 2 (max NR (max NG NF)), by omega, ?_⟩
  intro N hN L hband a b ha hab hcop hbb hheight xy hxy
  obtain ⟨hxyN, hu⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hxyN
  have hgeom := hg N (by omega) L hband
  have hL : 0 < L := by omega
  have hxpos : 0 < xy.1 := by have h := (mem_Ico.mp hx).1; omega
  have hypos : 0 < xy.2 := by have h := (mem_Ico.mp hy).1; omega
  have hloss := hr N (by omega) L a b xy.1 xy.2 hband ha hab.le hheight hx hy hu
  have hunitRaw := UnitFourierWeight.unit_kernel_rank_bound (L := L) ha (ha.trans hab) hcop hxpos hypos
  have hunit : (((units a b xy.1 xy.2 L).card - 1 : ℕ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / b₀ :=
    hunitRaw.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast hb₀)
      (by exact_mod_cast hbb))
  have hpower : (2 ^ pairLoss xy.1 xy.2 L : ℝ) ≤
      (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b₀) * (2 : ℝ) ^ (η * ((L + 1 : ℕ) : ℝ)) := by
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
    _ ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairLoss xy.1 xy.2 L : ℝ) := PairLossWeights.joint_bound hxpos hypos hL
    _ ≤ (((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 : ℝ)) *
        ((2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b₀) * (2 : ℝ) ^ (η * ((L + 1 : ℕ) : ℝ))) :=
      mul_le_mul (CriticalChannelPowers.nominal_square_upper (by omega) hband) hpower (by positivity) (by positivity)
    _ ≤ (((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 : ℝ)) *
        (((2 : ℝ) ^ ((C + 1) / b₀) * (N : ℝ) ^ (1 / (b₀ : ℝ))) *
          ((2 : ℝ) ^ (η * (C + 1)) * (N : ℝ) ^ η)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (CriticalChannelPowers.window_root_upper (by omega) hb₀ hband)
        hsmall (by positivity) (by positivity)) (by positivity)
    _ = K * (N : ℝ) ^ (-2 + 1 / (b₀ : ℝ) + η) := by
      rw [Real.rpow_add hn (-2 + 1 / (b₀ : ℝ)) η, Real.rpow_add hn (-2) (1 / (b₀ : ℝ))]
      dsimp [K]
      ring
    _ ≤ (N : ℝ) ^ ((-2 + 1 / (b₀ : ℝ) + η) + η) := hf N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_coefficient (b₀ : ℕ) (hb₀ : 0 < b₀) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ a b : ℕ,
      0 < a → a < b → a.Coprime b → b₀ ≤ b → b ≤ (L + 1) ^ 3 →
      ∀ xy ∈ unitSources N a b L,
      |infiniteCenteredCoefficient L {xy.1, xy.2}| ≤ (N : ℝ) ^ (-2 + 1 / (b₀ : ℝ) + ε) := by
  let K := 2 * (2 : ℝ) ^ C
  obtain ⟨NQ, _hNQ, hq⟩ := uniform_joint b₀ hb₀ C (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C 2 (by norm_num) 4
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (1 + K ^ 2) (-2 + 1 / (b₀ : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NQ (max NP (max NL NF))), by omega, ?_⟩
  intro N hN L hband a b ha hab hcop hbb hheight xy hxy
  obtain ⟨hx, hy⟩ := mem_product.mp (mem_filter.mp hxy).1
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlarge : (a + b) * (L + 1) < N := by
    have hpoly : 2 * (L + 1) ^ 4 < N := by exact_mod_cast hl N (by omega) L hband
    calc
      _ ≤ (2 * (L + 1) ^ 3) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * (L + 1) ^ 4 := by ring
      _ < _ := hpoly
  have hxyne := ne_of_lt (PairLossWeights.unit_order (by omega : 0 < N) hab hlarge hxy)
  have hprod : infiniteMarginal xy.1 L * infiniteMarginal xy.2 L ≤
      K ^ 2 * (N : ℝ) ^ (-2 + 1 / (b₀ : ℝ) + ε / 2) := by
    calc
      _ ≤ (K / N) * (K / N) := mul_le_mul (hp N (by omega) L hband xy.1 hx)
        (hp N (by omega) L hband xy.2 hy) (MissingBlockProbabilities.infiniteMarginal_nonneg xy.2 L) (by dsimp [K]; positivity)
      _ = K ^ 2 * (N : ℝ) ^ (-2 : ℝ) := by rw [Real.rpow_neg hn.le, Real.rpow_two]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by
        have hb : (0 : ℝ) ≤ 1 / (b₀ : ℝ) := by positivity
        linarith only [hb, hε])) (sq_nonneg K)
  calc
    _ ≤ infiniteJointMoment L {xy.1, xy.2} + infiniteMarginal xy.1 L * infiniteMarginal xy.2 L :=
      PairRowActivity.pair_absolute_bound L xy.1 xy.2 hxyne
    _ ≤ (1 + K ^ 2) * (N : ℝ) ^ (-2 + 1 / (b₀ : ℝ) + ε / 2) := by
      have h := hq N (by omega) L hband a b ha hab hcop hbb hheight xy hxy
      nlinarith only [h, hprod]
    _ ≤ (N : ℝ) ^ ((-2 + 1 / (b₀ : ℝ) + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.LogHeightUnitChannelWeights
