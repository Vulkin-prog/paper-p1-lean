module

public import PaperP1.Asymptotics.PrivateChannelMassRate
public import PaperP1.Asymptotics.ChannelMainTermBounds

/-! # The actual retained fixed-channel mass has its positive channel phase -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateChannelMassPhase

open PaperP1.PrivateChannelSources PaperP1.PrivateChannelMassRate PaperP1.ChannelMainTermBounds
  PaperP1.CriticalBandScale

theorem phase_bounds (C : ℝ) (D a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
        (lowerConstant C a b / 2) * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ channelMass N H a b L ∧
        channelMass N H a b L ≤ (upperConstant C a b + lowerConstant C a b / 2) * L *
          (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by
  have hb : 0 < b := ha.trans hab
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  let K := massConstant C b
  let c := lowerConstant C a b
  let d := upperConstant C a b
  have hK : 0 < K := massConstant_pos C b
  have hc : 0 < c := (constants_pos C ha hb hinterior).1
  obtain ⟨Nmass, hmass⟩ := mass_error_square_log C D a b ha hab hinterior hcop
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C (10 * b ^ 3 + 1)
  obtain ⟨Npoly, hpoly⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le (4 * K / c) 1 (1 / (b : ℝ)) (one_div_pos.mpr hbR)
  refine ⟨max Nmass (max Ngeom Npoly), ?_⟩
  intro N hN L H hcrit hcut hH
  obtain ⟨hNtwo, hBbig, _, _, _, hB⟩ := hgeom N (by omega) L hcrit
  have hLbig : 10 * b ^ 3 ≤ L := by omega
  have hLpos : 0 < L := by have hp := pow_pos hb 3; nlinarith only [hp, hLbig]
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hBtwo : ((L + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast (by omega : L + 1 ≤ 2 * L)
  have hp : (4 * K / c) * ((L + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / (b : ℝ)) := by
    have h := hpoly N (by omega) L hB
    simpa only [Nat.cast_add, Nat.cast_one, pow_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 * K / c) * (L + 1 : ℝ))] using h
  have hpDiv : 4 * K * ((L + 1 : ℕ) : ℝ) / c ≤ (N : ℝ) ^ (1 / (b : ℝ)) := by
    convert hp using 1; ring
  have hscaled := (div_le_iff₀ hc).mp hpDiv
  have h₁ := mul_le_mul_of_nonneg_left hBtwo (mul_nonneg hK.le (Nat.cast_nonneg (L + 1)))
  have h₂ := mul_le_mul_of_nonneg_right hscaled (by positivity : (0 : ℝ) ≤ (L : ℝ) / 2)
  have hNumerator : K * ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (c / 2) * L * (N : ℝ) ^ (1 / (b : ℝ)) := by
    nlinarith only [h₁, h₂]
  have hRelative : K * ((L + 1 : ℕ) : ℝ) ^ 2 / N ≤
      (c / 2) * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by
    calc
      _ ≤ ((c / 2) * L * (N : ℝ) ^ (1 / (b : ℝ))) / N := div_le_div_of_nonneg_right hNumerator hn.le
      _ = _ := by
        rw [show -1 + 1 / (b : ℝ) = 1 / (b : ℝ) - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
        ring
  have hm : |channelMass N H a b L - mainTerm N L a b| ≤ K * ((L + 1 : ℕ) : ℝ) ^ 2 / N :=
    hmass N (by omega) L H hcrit hcut hH
  have he := abs_le.mp (hm.trans hRelative)
  have hmain := main_term_bounds hNtwo ha hab hinterior hLbig hcrit
  change c * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ mainTerm N L a b ∧
    mainTerm N L a b ≤ d * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) at hmain
  change (c / 2) * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ channelMass N H a b L ∧
    channelMass N H a b L ≤ (d + c / 2) * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ))
  constructor <;> nlinarith only [he.1, he.2, hmain.1, hmain.2]

theorem positive_phase (C : ℝ) (D a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) :
    ∃ c k : ℝ, 0 < c ∧ 0 < k ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
        c * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ channelMass N H a b L ∧
        channelMass N H a b L ≤ k * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by
  obtain ⟨hc, hk⟩ := constants_pos C ha (ha.trans hab) hinterior
  obtain ⟨N₀, hN₀⟩ := phase_bounds C D a b ha hab hinterior hcop
  exact ⟨lowerConstant C a b / 2, upperConstant C a b + lowerConstant C a b / 2,
    by positivity, by positivity, N₀, hN₀⟩

end PaperP1.PrivateChannelMassPhase
