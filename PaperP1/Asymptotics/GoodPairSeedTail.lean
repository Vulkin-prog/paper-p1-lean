module

public import PaperP1.Model.PairExtensionSeedTail
public import PaperP1.Asymptotics.OriginalParticipatingTail
public import PaperP1.Model.FiniteGoodChannelPartition
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Asymptotics.CriticalPolynomialScale

/-! # All large relative seeds of actual finite-channel good pairs are controlled using original participating families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GoodPairSeedTail

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteAlignedChannelCover PaperP1.PrivateChannelSources PaperP1.PairExtensionSeedTail

theorem private_product {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) (hL : 0 < L)
    (e : Finset ℕ) (he : e ∈ PrivateChannelActivity.pairs N H a b L) (u : ℝ) :
    (∏ x ∈ e, u * infiniteMarginal x L) = u ^ 2 * ((2 ^ L : ℝ)⁻¹) ^ 2 := by
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  obtain ⟨hx, hy, _, hprivate⟩ := mem_goodSources.mp hxy
  obtain ⟨hpx, hpy⟩ := PrivateUnitCovariance.private_marginals ha (ha.trans hab)
    (hN.trans (mem_Ico.mp hx).1) (hN.trans (mem_Ico.mp hy).1) hL hprivate.private
  rw [prod_pair (ne_of_lt (good_sources_order hN hab hlarge hxy)), hpx, hpy]
  ring

theorem private_ratio {N H a b L : ℕ} {C u : ℝ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hb : 3 ≤ b) (hlarge : (a + b) * (L + 1) < N) (hL : 0 < L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) (hu : 0 < u)
    (e : Finset ℕ) (he : e ∈ PrivateChannelActivity.pairs N H a b L) :
    |infiniteCenteredCoefficient L e| ≤
      ((2 : ℝ) ^ ((C + 1) / 3) / u ^ 2 * (N : ℝ) ^ (1 / 3 : ℝ)) *
        ∏ x ∈ e, u * infiniteMarginal x L := by
  have hroot : (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) ≤
      (2 : ℝ) ^ ((C + 1) / 3) * (N : ℝ) ^ (1 / 3 : ℝ) := by
    apply le_trans _ (CriticalChannelPowers.window_root_upper (b := 3) hN (by decide) hband)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by exact_mod_cast hb)
  calc
    _ ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) :=
      PrivateChannelActivity.coefficient_bound hN ha hab hcop hlarge hL he
    _ ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 * ((2 : ℝ) ^ ((C + 1) / 3) * (N : ℝ) ^ (1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hroot (sq_nonneg _)
    _ = _ := by
      rw [private_product hN ha hab hlarge hL e he u]
      field_simp

theorem uniform_ratio (Q : ℕ) (C u : ℝ) (hu : 0 < u) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e ∈ FiniteGoodChannelPartition.good Q N (2 * Q * (L + 1)) L,
      |infiniteCenteredCoefficient L e| ≤
        ((2 : ℝ) ^ ((C + 1) / 3) / u ^ 2 * (N : ℝ) ^ (1 / 3 : ℝ)) *
          ∏ x ∈ e, u * infiniteMarginal x L := by
  obtain ⟨NP, hp⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((2 * Q : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NP + NG, by omega, ?_⟩
  intro N hN L hband e he
  obtain ⟨_, _, ab, hab, heab⟩ := FiniteGoodChannelPartition.good_data he
  obtain ⟨ha, hlt, _hint, hcop, hb, hbQ⟩ := channel_data hab
  have hlarge : (ab.1 + ab.2) * (L + 1) < N := by
    have h := hp N (by omega) L hband
    have hnat : 2 * Q * (L + 1) < N := by
      simpa only [pow_one, ← Nat.cast_mul, Nat.cast_lt] using h
    exact (Nat.mul_le_mul_right (L + 1) (by omega : ab.1 + ab.2 ≤ 2 * Q)).trans_lt hnat
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  exact private_ratio (by omega) ha hlt hcop hb hlarge hL hband hu e heab

theorem uniform_large_seeds (Q : ℕ) (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ e ∈ FiniteGoodChannelPartition.good Q N (2 * Q * (L + 1)) L,
        |infiniteCenteredCoefficient L e| * ∑ A ∈ largeSeeds (dyadicBlock N) L e s,
          ∏ x ∈ A, u * infiniteMarginal x L) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  let M := 4 * u * (2 : ℝ) ^ C
  let K := (2 : ℝ) ^ ((C + 1) / 3) / u ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨s, hs, NT, _hNT, ht⟩ := OriginalParticipatingTail.subcritical_tail C M (23 / 12) (ε / 2)
    hM (by norm_num) (by positivity)
  obtain ⟨NR, _hNR, hr⟩ := uniform_ratio Q C u hu
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨s, hs, 10 + NT + NR + NM + NF, by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hw : ∀ x, 0 ≤ u * infiniteMarginal x L := fun x ↦
    mul_nonneg hu.le (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have hcap : ∀ x ∈ dyadicBlock N, 2 * (u * infiniteMarginal x L) ≤ M / N := by
    intro x hx
    have h := mul_le_mul_of_nonneg_left (hm N (by omega) L hband x hx) (by positivity : 0 ≤ 2 * u)
    calc
      _ ≤ (2 * u) * (2 * (2 : ℝ) ^ C / N) := by simpa only [mul_assoc] using h
      _ = _ := by dsimp [M]; ring
  have htail := ht N (by omega) L hband (fun x ↦ 2 * (u * infiniteMarginal x L))
    (fun x ↦ mul_nonneg (by norm_num) (hw x)) hcap (participating (dyadicBlock N) L s)
    (fun I hI ↦ (mem_participating _ _ _ _).mp hI)
  have hweighted := weighted_bound (dyadicBlock N) L s
    (FiniteGoodChannelPartition.good Q N (2 * Q * (L + 1)) L) (by
      intro e he
      have hdep := FiniteGoodChannelPartition.good_subset Q N (2 * Q * (L + 1)) L he
      obtain ⟨hecard, hepos⟩ := mem_filter.mp hdep
      obtain ⟨hesub, hecard⟩ := mem_powersetCard.mp hecard
      exact ⟨hesub, hecard, hepos⟩)
    (fun x ↦ u * infiniteMarginal x L) (fun e ↦ |infiniteCenteredCoefficient L e|)
    (K * (N : ℝ) ^ (1 / 3 : ℝ)) hw (mul_nonneg hK (Real.rpow_nonneg hn.le _))
    (fun e he ↦ ⟨abs_nonneg _, hr N (by omega) L hband e he⟩)
  calc
    _ ≤ (K * (N : ℝ) ^ (1 / 3 : ℝ)) * (N : ℝ) ^ (-(23 / 12) + ε / 2) :=
      hweighted.trans (mul_le_mul_of_nonneg_left htail (mul_nonneg hK (Real.rpow_nonneg hn.le _)))
    _ = K * (N : ℝ) ^ ((1 / 3 : ℝ) + (-(23 / 12) + ε / 2)) := by
      rw [mul_assoc, ← Real.rpow_add hn]
    _ ≤ K * (N : ℝ) ^ (-3 / 2 + ε / 2) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) hK
    _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.GoodPairSeedTail
