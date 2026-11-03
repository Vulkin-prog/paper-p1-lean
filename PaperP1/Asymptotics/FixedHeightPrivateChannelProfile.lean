module

public import PaperP1.Model.FixedHeightPrivateChannels
public import PaperP1.Asymptotics.PrivateChannelMassRate
public import PaperP1.Asymptotics.PrivateChannelActivityRate
public import PaperP1.Asymptotics.PairActivitySignGap

/-! # The full retained finite channel sum has its literal explicit profile with rate one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedHeightPrivateChannelProfile

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteAlignedChannelCover PaperP1.PrivateChannelSources

theorem uniform_geometry (Q : ℕ) (hQ : 3 ≤ Q) (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * Q * (L + 1) < N ∧ 4 * Q ^ 2 * (L + 1) < N := by
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((4 * Q ^ 2 : ℕ) : ℝ)
    (Nat.cast_nonneg _) 1
  refine ⟨max 2 (max NG NP), by omega, ?_⟩
  intro N hN L hband
  have hlarge : 4 * Q ^ 2 * (L + 1) < N := by
    have h := hp N (by omega) L hband
    simpa only [pow_one, ← Nat.cast_mul, Nat.cast_lt] using h
  have hcoeff : 2 * Q ≤ 4 * Q ^ 2 := by nlinarith only [hQ]
  exact ⟨(Nat.mul_le_mul_right (L + 1) hcoeff).trans_lt hlarge, hlarge⟩

theorem uniform_comparison (Q : ℕ) (hQ : 3 ≤ Q) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |2 * CompatibleActivitySplit.signed L (privatePairs Q N (2 * Q * (L + 1)) L) -
        FiniteChannelHierarchy.coefficient N L Q| ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  have heach (ab : ℕ × ℕ) (hab : ab ∈ channels Q) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |2 * CompatibleActivitySplit.absolute L (PrivateChannelActivity.pairs N (2 * Q * (L + 1)) ab.1 ab.2 L) -
        ChannelMainTermBounds.mainTerm N L ab.1 ab.2| ≤ 3 * (N : ℝ) ^ (-1 + ε / 2) := by
    obtain ⟨ha, hlt, hint, hcop, _hb, hbQ⟩ := channel_data hab
    obtain ⟨NA, _hNA, ha₀⟩ := PrivateChannelActivityRate.uniform_absolute_comparison C (ε / 2)
      ab.1 ab.2 ha hlt (by positivity)
    obtain ⟨NM, hm⟩ := PrivateChannelMassRate.mass_error_rpow C (2 * Q) ab.1 ab.2
      ha hlt hint hcop (ε / 2) (by positivity)
    refine eventually_atTop.mpr ⟨max NA NM, ?_⟩
    intro N hN L hband
    have hcut : 2 * ab.2 * (L + 1) ≤ 2 * Q * (L + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hbQ)
    have hA := ha₀ N (by omega) L (2 * Q * (L + 1)) hband
    have hM := hm N (by omega) L (2 * Q * (L + 1)) hband hcut le_rfl
    change |channelMass N (2 * Q * (L + 1)) ab.1 ab.2 L - ChannelMainTermBounds.mainTerm N L ab.1 ab.2| ≤ _ at hM
    exact abs_le.mpr ⟨by linarith only [(abs_le.mp hA).1, (abs_le.mp hM).1],
      by linarith only [(abs_le.mp hA).2, (abs_le.mp hM).2]⟩
  obtain ⟨NE, he⟩ := eventually_atTop.mp ((Finset.eventually_all (channels Q)).mpr heach)
  obtain ⟨NG, _hNG, hg⟩ := uniform_geometry Q hQ C
  obtain ⟨NS, _hNS, hs⟩ := PairActivitySignGap.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (3 * ((channels Q).card : ℝ) + 2)
    (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NE (max NG (max NS NF))), by omega, ?_⟩
  intro N hN L hband
  obtain ⟨hsmall, hlarge⟩ := hg N (by omega) L hband
  have hsub := FixedHeightPrivateChannels.private_subset (H := 2 * Q * (L + 1)) (by omega : 2 ≤ N) hsmall
  have hsign := hs N (by omega) L hband _ hsub
  have hsum : |2 * CompatibleActivitySplit.absolute L (privatePairs Q N (2 * Q * (L + 1)) L) -
      FiniteChannelHierarchy.coefficient N L Q| ≤
        3 * ((channels Q).card : ℝ) * (N : ℝ) ^ (-1 + ε / 2) := by
    rw [FixedHeightPrivateChannels.absolute_private_sum (by omega) hlarge,
      ← FixedHeightPrivateChannels.main_terms Q N L (by omega), mul_sum, ← sum_sub_distrib]
    calc
      _ ≤ ∑ ab ∈ channels Q,
          |2 * CompatibleActivitySplit.absolute L (PrivateChannelActivity.pairs N (2 * Q * (L + 1)) ab.1 ab.2 L) -
            ChannelMainTermBounds.mainTerm N L ab.1 ab.2| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ab ∈ channels Q, 3 * (N : ℝ) ^ (-1 + ε / 2) :=
        sum_le_sum fun ab hab ↦ he N (by omega) ab hab L hband
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  have hfinal : |2 * CompatibleActivitySplit.signed L (privatePairs Q N (2 * Q * (L + 1)) L) -
      FiniteChannelHierarchy.coefficient N L Q| ≤
        (3 * ((channels Q).card : ℝ) + 2) * (N : ℝ) ^ (-1 + ε / 2) := by
    exact abs_le.mpr ⟨by linarith only [(abs_le.mp hsum).1, hsign.2],
      by linarith only [(abs_le.mp hsum).2, hsign.1, Real.rpow_nonneg (Nat.cast_nonneg N) (-1 + ε / 2)]⟩
  calc
    _ ≤ _ := hfinal
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.FixedHeightPrivateChannelProfile
