module

public import PaperP1.Asymptotics.ChannelWordPhase

/-! # The literal omitted-height leading term with all moving parameters

The channel height is fixed; the actual residue, nominal mean and critical
length all vary after the common threshold. No pair remainder is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelMassPhaseEquivalent

open PaperP1.FiniteChannelHierarchy PaperP1.ChannelPhaseConstants PaperP1.ChannelWordPhase

def heightMass (N L b : ℕ) : ℝ := (nominalMean N L) ^ 2 / N * heightSum b L

def phaseMass (N L b : ℕ) : ℝ := phaseConstant b (L % b) *
  (nominalMean N L) ^ (2 - 1 / (b : ℝ)) * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ))

theorem nominal_power_identity (N L b : ℕ) (hN : 0 < N) :
    (nominalMean N L) ^ (2 - 1 / (b : ℝ)) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) =
      (nominalMean N L) ^ 2 / N * (2 : ℝ) ^ ((L : ℝ) / b) := by
  let t := 1 / (b : ℝ)
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hμ : 0 < nominalMean N L := by unfold nominalMean; positivity
  have hquot : (N : ℝ) / nominalMean N L = (2 : ℝ) ^ L := by
    unfold nominalMean
    field_simp
  have hpow : ((2 : ℝ) ^ L) ^ t = (2 : ℝ) ^ ((L : ℝ) / b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    dsimp only [t]
    ring
  change (nominalMean N L) ^ (2 - t) * (N : ℝ) ^ (-1 + t) = _
  calc
    _ = ((nominalMean N L) ^ 2 / (nominalMean N L) ^ t) * ((N : ℝ) ^ t / N) := by
      rw [Real.rpow_sub hμ, Real.rpow_two,
        show -1 + t = t - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
    _ = (nominalMean N L) ^ 2 / N * ((N : ℝ) ^ t / (nominalMean N L) ^ t) := by ring
    _ = (nominalMean N L) ^ 2 / N * ((N : ℝ) / nominalMean N L) ^ t := by
      rw [Real.div_rpow hn.le hμ.le]
    _ = _ := by rw [hquot, hpow]

theorem phaseMass_eq_word (N L b : ℕ) (hN : 0 < N) :
    phaseMass N L b = (nominalMean N L) ^ 2 / N * wordMain b L := by
  unfold phaseMass wordMain
  calc
    _ = phaseConstant b (L % b) * L *
        ((nominalMean N L) ^ (2 - 1 / (b : ℝ)) * (N : ℝ) ^ (-1 + 1 / (b : ℝ))) := by ring
    _ = _ := by rw [nominal_power_identity N L b hN]; ring

theorem phaseMass_pos (N L b : ℕ) (hN : 0 < N) (hL : 0 < L) (hb : 3 ≤ b) :
    0 < phaseMass N L b := by
  rw [phaseMass_eq_word N L b hN]
  have hμ : 0 < nominalMean N L := by unfold nominalMean; positivity
  exact mul_pos (by positivity) (wordMain_pos b L hb hL)

theorem uniform_relative (C : ℝ) (b : ℕ) (hb : 3 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |heightMass N L b - phaseMass N L b| ≤ ε * phaseMass N L b := by
  obtain ⟨N₀, hN₀, hrelative⟩ := uniform_critical_relative C b hb ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  have hNpos : 0 < N := by omega
  have hf : 0 ≤ (nominalMean N L) ^ 2 / N := by positivity
  rw [phaseMass_eq_word N L b hNpos, heightMass]
  calc
    _ = (nominalMean N L) ^ 2 / N * |heightSum b L - wordMain b L| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hf]
    _ ≤ (nominalMean N L) ^ 2 / N * (ε * wordMain b L) :=
      mul_le_mul_of_nonneg_left (hrelative N hN L hband) hf
    _ = _ := by ring

theorem uniform_ratio (C : ℝ) (b : ℕ) (hb : 3 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < phaseMass N L b ∧ |heightMass N L b / phaseMass N L b - 1| ≤ ε := by
  obtain ⟨NA, hNA, hrelative⟩ := uniform_relative C b hb ε hε
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max NA NG, by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hp := phaseMass_pos N L b (by omega) hL hb
  refine ⟨hp, ?_⟩
  have heq : heightMass N L b / phaseMass N L b - 1 =
      (heightMass N L b - phaseMass N L b) / phaseMass N L b := by field_simp
  rw [heq, abs_div, abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr (hrelative N (by omega) L hband)

end PaperP1.ChannelMassPhaseEquivalent
