module

public import PaperP1.Model.PrivateChannelMassBound
public import PaperP1.Arithmetic.ChannelUnsignedBound
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Asymptotics.FixedChannelErrorAlgebra
public import PaperP1.Asymptotics.NormalizedDefectSourceCount
public import PaperP1.Asymptotics.CriticalPolynomialScale

/-! # Actual fixed-channel mass has an explicit square-logarithmic remainder -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateChannelMassRate

open PaperP1.Model PaperP1.PrivateChannelSources PaperP1.PrivateChannelMassBound
  PaperP1.NormalizedDefectSources PaperP1.CriticalChannelPowers PaperP1.ChannelUnsignedBound
  PaperP1.CriticalBandScale

def massConstant (C : ℝ) (b : ℕ) : ℝ := ((2 : ℝ) ^ C) ^ 2 * (8 * (2 : ℝ) ^ ((C + 1) / b) + 2)

theorem massConstant_pos (C : ℝ) (b : ℕ) : 0 < massConstant C b := by
  unfold massConstant
  positivity

theorem mass_error_square_log (C : ℝ) (D a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
        |channelMass N H a b L - ((2 ^ L : ℝ)⁻¹) ^ 2 *
          ((N : ℝ) * (ActualSourceTranslations.coefficient a b : ℝ) * (ChannelSumIdentity.signed L a b : ℤ))| ≤
          massConstant C b * ((L + 1 : ℕ) : ℝ) ^ 2 / N := by
  have hb : 0 < b := ha.trans hab
  have hb3 : 3 ≤ b := by omega
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Nbad, hbad⟩ := NormalizedDefectSourceCount.bad_sources_rate C D a b ha hb hab.le (1 / 12) (by norm_num)
  obtain ⟨Npoly, hpoly⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 1 1 (2 / 3) (by norm_num)
  obtain ⟨Nlarge, hlarge⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  refine ⟨max Ngeom (max Nbad (max Npoly Nlarge)), ?_⟩
  intro N hN L H hcrit hcut hH
  obtain ⟨hNtwo, _, hBtwo, _, _, hB⟩ := hgeom N (by omega) L hcrit
  have hL : 0 < L := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlargeN : (a + b) * (L + 1) < N := by
    have h := hlarge N (by omega) L hcrit
    simp only [pow_one] at h
    exact_mod_cast h
  have hBpower : ((L + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
    have hp := hpoly N (by omega) L hB
    simpa only [Nat.cast_add, Nat.cast_one, one_mul, pow_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ L + 1)] using hp
  have hbadCount : ((badSources N H a b L).card : ℝ) ≤ (N : ℝ) ^ (7 / 12 : ℝ) := by
    convert hbad N (by omega) L H hcrit hcut hH using 1; norm_num
  let Kp : ℝ := ((2 : ℝ) ^ C) ^ 2
  let K₀ : ℝ := (2 : ℝ) ^ ((C + 1) / b)
  have hR : (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) ≤ K₀ * (N : ℝ) ^ (1 / 3 : ℝ) := by
    have hroot := window_root_upper hNtwo hb hcrit
    have he : (1 / (b : ℝ)) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hb3)
    exact hroot.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 he) (by positivity))
  have hU : ((ChannelSumIdentity.unsigned L a b : ℤ) : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) ^ 2 * K₀ * (N : ℝ) ^ (1 / 3 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hR (sq_nonneg (((L + 1 : ℕ) : ℝ)))
    have hu := unsigned_upper_rpow (L := L) hb hab.le
    nlinarith only [hu, hm]
  have hUpos : (0 : ℝ) ≤ (ChannelSumIdentity.unsigned L a b : ℤ) := by
    exact_mod_cast ChannelWordHosts.unsigned_nonneg (L := L) hb hab.le
  have hscale := FixedChannelErrorAlgebra.error_scale hn1
    (by exact_mod_cast (by omega : 1 ≤ L + 1)) hUpos (Nat.cast_nonneg ((badSources N H a b L).card))
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (by positivity : 0 ≤ Kp) (by positivity : 0 ≤ K₀)
    (nominal_square_upper hNtwo hcrit) hU hbadCount hR hBpower
  have hfinite := finite_mass_error (H := H) hNtwo ha hab hinterior hcop hlargeN hL
  have ht := hfinite.trans hscale
  simpa only [massConstant, Kp, K₀, Real.rpow_neg_one, div_eq_mul_inv] using ht

theorem mass_error_rpow (C : ℝ) (D a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * b * (L + 1) ≤ H → H ≤ D * (L + 1) →
        |channelMass N H a b L - ((2 ^ L : ℝ)⁻¹) ^ 2 *
          ((N : ℝ) * (ActualSourceTranslations.coefficient a b : ℝ) * (ChannelSumIdentity.signed L a b : ℤ))| ≤
          (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨Nmass, hmass⟩ := mass_error_square_log C D a b ha hab hinterior hcop
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Npoly, hpoly⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le (massConstant C b) 2 ε hε
  refine ⟨max Nmass (max Ngeom Npoly), ?_⟩
  intro N hN L H hcrit hcut hH
  obtain ⟨hNtwo, _, _, _, _, hB⟩ := hgeom N (by omega) L hcrit
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp : massConstant C b * ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ ε := by
    have h := hpoly N (by omega) L hB
    simpa only [Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (mul_nonneg (massConstant_pos C b).le (sq_nonneg (L + 1 : ℝ)))] using h
  calc
    _ ≤ massConstant C b * ((L + 1 : ℕ) : ℝ) ^ 2 / N := hmass N (by omega) L H hcrit hcut hH
    _ ≤ (N : ℝ) ^ ε / N := div_le_div_of_nonneg_right hp hn.le
    _ = _ := by rw [show -1 + ε = ε - 1 by ring, Real.rpow_sub hn, Real.rpow_one]

end PaperP1.PrivateChannelMassRate
