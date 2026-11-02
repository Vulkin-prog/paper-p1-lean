module

public import PaperP1.Model.PrivateChannelActivity
public import PaperP1.Asymptotics.PrivateChannelMassPhase
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Unconditional individual and total centered activity in each fixed good channel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateChannelActivityRate

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrivateChannelSources
  PaperP1.PrivateChannelActivity PaperP1.CriticalChannelPowers

theorem uniform_independent_mass (C ε : ℝ) (a b : ℕ) (ha : 0 < a) (hab : a < b) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      independentMass N H a b L ≤ (N : ℝ) ^ (-1 + ε) := by
  let K : ℝ := ((2 : ℝ) ^ C) ^ 2
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨NP, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (K * CriticalBandScale.upperScale ^ 2) 2 ε hε
  refine ⟨max 2 (max NG (max NP NL)), by omega, ?_⟩
  intro N hN L H hband
  obtain ⟨hNtwo, _, hBtwo, _, _, hB⟩ := hg N (by omega) L hband
  have hL : 0 < L := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlarge : (a + b) * (L + 1) < N := by
    have h := hl N (by omega) L hband
    simpa only [pow_one, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_lt] using h
  have hpoly : K * ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ ε := by
    calc
      _ ≤ K * (CriticalBandScale.upperScale * Real.log N) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hB 2) (by dsimp [K]; positivity)
      _ = K * CriticalBandScale.upperScale ^ 2 * (Real.log N) ^ 2 := by ring
      _ ≤ _ := by simpa only [Real.rpow_two] using hp N (by omega)
  calc
    _ = ((2 ^ L : ℝ)⁻¹) ^ 2 * (goodSources N H a b L).card := independent_mass_eq hNtwo ha hab hlarge hL
    _ ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 * (((L + 1 : ℕ) : ℝ) ^ 2 * N) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact_mod_cast good_sources_card (by omega : 0 < N) ha
    _ ≤ (K * (N : ℝ) ^ (-2 : ℝ)) * (((L + 1 : ℕ) : ℝ) ^ 2 * N) :=
      mul_le_mul_of_nonneg_right (nominal_square_upper hNtwo hband) (by positivity)
    _ = K * ((L + 1 : ℕ) : ℝ) ^ 2 / N := by
      rw [Real.rpow_neg hn.le, Real.rpow_two]
      field_simp
    _ ≤ (N : ℝ) ^ ε / N := div_le_div_of_nonneg_right hpoly hn.le
    _ = _ := by rw [show -1 + ε = ε - 1 by ring, Real.rpow_sub hn, Real.rpow_one]

theorem uniform_coefficient (C ε : ℝ) (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ e ∈ pairs N H a b L,
      |infiniteCenteredCoefficient L e| ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
  let K : ℝ := ((2 : ℝ) ^ C) ^ 2 * (2 : ℝ) ^ ((C + 1) / b)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K (-2 + 1 / (b : ℝ)) ε hε
  refine ⟨max 2 (max NG (max NL NF)), by omega, ?_⟩
  intro N hN L H hband e he
  have hNtwo := (hg N (by omega) L hband).1
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hlarge : (a + b) * (L + 1) < N := by
    have h := hl N (by omega) L hband
    simpa only [pow_one, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_lt] using h
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) :=
      coefficient_bound hNtwo ha hab hcop hlarge hL he
    _ ≤ (((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 : ℝ)) *
        ((2 : ℝ) ^ ((C + 1) / b) * (N : ℝ) ^ (1 / (b : ℝ))) :=
      mul_le_mul (nominal_square_upper hNtwo hband) (window_root_upper hNtwo (ha.trans hab) hband)
        (by positivity) (by positivity)
    _ = K * (N : ℝ) ^ (-2 + 1 / (b : ℝ)) := by
      rw [Real.rpow_add hn]
      dsimp [K]
      ring
    _ ≤ _ := hf N (by omega)

theorem uniform_absolute_comparison (C ε : ℝ) (a b : ℕ) (ha : 0 < a) (hab : a < b) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |CompatibleActivitySplit.absolute L (pairs N H a b L) - channelMass N H a b L / 2| ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NI, hNI, hi⟩ := uniform_independent_mass C ε a b ha hab hε
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  refine ⟨max NI NL, by omega, ?_⟩
  intro N hN L H hband
  have hlarge : (a + b) * (L + 1) < N := by
    have h := hl N (by omega) L hband
    simpa only [pow_one, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_lt] using h
  exact (absolute_comparison (by omega) hab hlarge).trans (hi N (by omega) L H hband)

theorem uniform_activity (C ε : ℝ) (D a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
      CompatibleActivitySplit.absolute L (pairs N H a b L) ≤
        (N : ℝ) ^ (-1 + 1 / (b : ℝ) + ε) := by
  obtain ⟨c, k, _hc, hk, NM, hm⟩ := PrivateChannelMassPhase.positive_phase C D a b ha hab hinterior hcop
  obtain ⟨NI, _hNI, hi⟩ := uniform_absolute_comparison C (ε / 2) a b ha hab (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    ((k / 2) * CriticalBandScale.upperScale) 1 (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NM (max NI (max NG (max NP NF)))), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hB := (hg N (by omega) L hband).2.2.2.2.2
  have hLB : (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ L
  have hL : (L : ℝ) ≤ CriticalBandScale.upperScale * Real.log N := hLB.trans hB
  have hpoly : (k / 2) * L ≤ (N : ℝ) ^ (ε / 2) :=
    (mul_le_mul_of_nonneg_left hL (by positivity)).trans
      (by simpa only [Real.rpow_one, mul_assoc] using hp N (by omega))
  have hmass := (hm N (by omega) L H hband hcut hH).2
  have hgap := (abs_le.mp (hi N (by omega) L H hband)).2
  have hbase : (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + 1 / (b : ℝ) + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by
      have hb : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
      linarith only [hb])
  have hmain : channelMass N H a b L / 2 ≤ (N : ℝ) ^ (-1 + 1 / (b : ℝ) + ε / 2) := by
    calc
      _ ≤ ((k / 2) * L) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by linarith only [hmass]
      _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) :=
        mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  calc
    _ ≤ 2 * (N : ℝ) ^ (-1 + 1 / (b : ℝ) + ε / 2) := by linarith only [hgap, hbase, hmain]
    _ ≤ (N : ℝ) ^ ((-1 + 1 / (b : ℝ) + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PrivateChannelActivityRate
