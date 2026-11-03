module

public import PaperP1.Model.PrivateChannelPositiveMass
public import PaperP1.Asymptotics.NormalizedDefectSourceCount
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Asymptotics.HalfCountSchedule
public import PaperP1.Arithmetic.ChannelUnsignedBound

/-! # A private channel has its literal positive source profile with a sublinear error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateChannelPositiveProfile

open PaperP1.Model PaperP1.PrivateChannelPositiveMass PaperP1.NormalizedDefectSources
  PaperP1.CriticalBandScale PaperP1.CriticalChannelPowers

theorem uniform_error (C ε : ℝ) (D a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
      |channelWeight N H a b L -
        (N : ℝ) * (ActualSourceTranslations.coefficient a b : ℝ) * (ChannelSumIdentity.unsigned L a b : ℤ)| ≤
        (N : ℝ) ^ (1 / 2 + 1 / (b : ℝ) + ε) := by
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let K : ℝ := (2 : ℝ) ^ ((C + 1) / b)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NB, hb⟩ := NormalizedDefectSourceCount.bad_sources_rate C D a b ha (ha.trans hab) hab.le δ hδ
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le (6 * K) 3 δ hδ
  obtain ⟨NK, hk⟩ := HalfCountSchedule.factor_absorption K (1 / (b : ℝ)) δ hδ
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (1 / 2 + 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NG (max NB (max NL (max NP (max NK NF))))), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hB := (hg N (by omega) L hband).2.2.2.2.2
  have hlarge : (a + b) * (L + 1) < N := by
    have h := hl N (by omega) L hband
    simp only [pow_one] at h
    exact_mod_cast h
  have hroot : (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) ≤ K * (N : ℝ) ^ (1 / (b : ℝ)) :=
    window_root_upper (by omega) (ha.trans hab) hband
  have hpoly : 6 * K * ((L + 1 : ℕ) : ℝ) ^ 3 ≤ (N : ℝ) ^ δ := by
    have h := hp N (by omega) L hB
    simpa only [Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 6 * K * (L + 1 : ℝ) ^ 3)] using h
  have hendpoint : 6 * ((L + 1 : ℕ) : ℝ) * (ChannelSumIdentity.unsigned L a b : ℤ) ≤
      (N : ℝ) ^ (1 / (b : ℝ) + δ) := by
    calc
      _ ≤ 6 * ((L + 1 : ℕ) : ℝ) *
          (((L + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b)) :=
        mul_le_mul_of_nonneg_left (ChannelUnsignedBound.unsigned_upper_rpow (ha.trans hab) hab.le) (by positivity)
      _ ≤ 6 * ((L + 1 : ℕ) : ℝ) *
          (((L + 1 : ℕ) : ℝ) ^ 2 * (K * (N : ℝ) ^ (1 / (b : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hroot (sq_nonneg _)) (by positivity)
      _ = (6 * K * ((L + 1 : ℕ) : ℝ) ^ 3) * (N : ℝ) ^ (1 / (b : ℝ)) := by ring
      _ ≤ (N : ℝ) ^ δ * (N : ℝ) ^ (1 / (b : ℝ)) :=
        mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  have hbad : ((badSources N H a b L).card : ℝ) * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) ≤
      (N : ℝ) ^ (1 / 2 + 1 / (b : ℝ) + ε / 2) := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 2 + δ) * (N : ℝ) ^ (1 / (b : ℝ) + δ) :=
        mul_le_mul (hb N (by omega) L H hband hcut hH) (hroot.trans (hk N (by omega)))
          (by positivity) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; dsimp [δ]; ring
  have hendpoint' : 6 * ((L + 1 : ℕ) : ℝ) * (ChannelSumIdentity.unsigned L a b : ℤ) ≤
      (N : ℝ) ^ (1 / 2 + 1 / (b : ℝ) + ε / 2) := hendpoint.trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [δ]; linarith))
  have hfinite := finite_weight_error (H := H) (by omega : 2 ≤ N) ha hab hinterior hcop hlarge
  calc
    _ ≤ 3 * (N : ℝ) ^ (1 / 2 + 1 / (b : ℝ) + ε / 2) := by
      nlinarith only [hfinite, hendpoint', hbad]
    _ ≤ (N : ℝ) ^ ((1 / 2 + 1 / (b : ℝ) + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PrivateChannelPositiveProfile
