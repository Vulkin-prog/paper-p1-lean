module

public import PaperP1.Asymptotics.SignedChannelPhaseLimit
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import Mathlib.Order.Filter.Finite

/-! # The moving-residue leading equivalent of the literal finite height sum

Residue limits are assembled over the actual finite residue set. The final
threshold precedes every critical length, with no fixed-residue restriction.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelWordPhase

open Finset Filter PaperP1.FiniteChannelHierarchy PaperP1.ChannelPhaseConstants
  PaperP1.SignedChannelPhaseLimit

def wordMain (b L : ℕ) : ℝ :=
  phaseConstant b (L % b) * L * (2 : ℝ) ^ ((L : ℝ) / b)

theorem wordMain_pos (b L : ℕ) (hb : 3 ≤ b) (hL : 0 < L) : 0 < wordMain b L := by
  unfold wordMain
  exact mul_pos (mul_pos (phaseConstant_pos b (L % b) hb) (by exact_mod_cast hL))
    (Real.rpow_pos_of_pos (by norm_num) _)

theorem word_power_identity (b q r : ℕ) (hb : 0 < b) :
    (2 : ℝ) ^ (((b * q + r : ℕ) : ℝ) / b) =
      (2 : ℝ) ^ q * (2 : ℝ) ^ ((r : ℝ) / b) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have he : (((b * q + r : ℕ) : ℝ) / b) = (q : ℝ) + (r : ℝ) / b := by
    push_cast
    field_simp
  rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]

theorem normalized_wordMain_identity {b q r : ℕ} (hb : 3 ≤ b) (hq : 1 ≤ q) (hr : r < b) :
    wordMain b (b * q + r) / ((q : ℝ) * (2 : ℝ) ^ q) =
      phaseConstant b r * ((b : ℝ) + (r : ℝ) * (q : ℝ)⁻¹) *
        (2 : ℝ) ^ ((r : ℝ) / b) := by
  have hmod : (b * q + r) % b = r := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hqn : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [wordMain, hmod, word_power_identity b q r (by omega)]
  push_cast
  field_simp

theorem phase_normalization (b r : ℕ) (hb : 3 ≤ b) :
    phaseConstant b r * b * (2 : ℝ) ^ ((r : ℝ) / b) =
      (((b : ℝ) + r - 1) / b) * phaseSum b := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  rw [phaseConstant]
  field_simp

theorem tendsto_wordMain_normalized (b r : ℕ) (hb : 3 ≤ b) (hr : r < b) :
    Tendsto (fun q : ℕ ↦ wordMain b (b * q + r) / ((q : ℝ) * (2 : ℝ) ^ q)) atTop
      (nhds ((((b : ℝ) + r - 1) / b) * phaseSum b)) := by
  have hi : Tendsto (fun q : ℕ ↦ (q : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := (((hi.const_mul (r : ℝ)).const_add (b : ℝ)).const_mul (phaseConstant b r)).mul_const
    ((2 : ℝ) ^ ((r : ℝ) / b))
  have ht' : Tendsto (fun q : ℕ ↦ phaseConstant b r *
      ((b : ℝ) + (r : ℝ) * (q : ℝ)⁻¹) * (2 : ℝ) ^ ((r : ℝ) / b)) atTop
      (nhds ((((b : ℝ) + r - 1) / b) * phaseSum b)) := by
    simpa only [mul_zero, add_zero, phase_normalization b r hb] using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  exact (normalized_wordMain_identity hb hq hr).symm

theorem tendsto_ratio_residue (b r : ℕ) (hb : 3 ≤ b) (hr : r < b) :
    Tendsto (fun q : ℕ ↦ heightSum b (b * q + r) / wordMain b (b * q + r)) atTop (nhds 1) := by
  have hlim : 0 < (((b : ℝ) + r - 1) / b) * phaseSum b := by
    rw [← phase_normalization b r hb]
    have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    exact mul_pos (mul_pos (phaseConstant_pos b r hb) hbR) (Real.rpow_pos_of_pos (by norm_num) _)
  have ht := (tendsto_height_normalized b r hb hr).div (tendsto_wordMain_normalized b r hb hr) hlim.ne'
  have ht' : Tendsto (fun q : ℕ ↦
      (heightSum b (b * q + r) / ((q : ℝ) * (2 : ℝ) ^ q)) /
        (wordMain b (b * q + r) / ((q : ℝ) * (2 : ℝ) ^ q))) atTop (nhds 1) := by
    change Tendsto (fun q : ℕ ↦
      (heightSum b (b * q + r) / ((q : ℝ) * (2 : ℝ) ^ q)) /
        (wordMain b (b * q + r) / ((q : ℝ) * (2 : ℝ) ^ q))) atTop
      (nhds (((((b : ℝ) + r - 1) / b) * phaseSum b) /
        ((((b : ℝ) + r - 1) / b) * phaseSum b))) at ht
    simpa only [div_self hlim.ne'] using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  exact div_div_div_cancel_right₀ (by positivity : (q : ℝ) * (2 : ℝ) ^ q ≠ 0) _ _

theorem uniform_ratio_lengths (b : ℕ) (hb : 3 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, |heightSum b L / wordMain b L - 1| ≤ ε := by
  have he (r : ℕ) (hr : r ∈ range b) :
      ∀ᶠ q : ℕ in atTop, |heightSum b (b * q + r) / wordMain b (b * q + r) - 1| < ε := by
    have ht := ((tendsto_ratio_residue b r hb (mem_range.mp hr)).sub
      (tendsto_const_nhds (x := (1 : ℝ)))).abs
    have ht' : Tendsto (fun q : ℕ ↦
        |heightSum b (b * q + r) / wordMain b (b * q + r) - 1|) atTop (nhds 0) := by
      simpa only [sub_self, abs_zero] using ht
    exact ht'.eventually (eventually_lt_nhds hε)
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp ((Finset.eventually_all (range b)).mpr he)
  refine ⟨b * (Q + 1), Nat.mul_pos (by omega : 0 < b) (by omega : 0 < Q + 1), ?_⟩
  intro L hL
  have hbpos : 0 < b := by omega
  have hq : Q ≤ L / b := (Nat.le_div_iff_mul_le hbpos).mpr (by nlinarith only [hL])
  have hr : L % b ∈ range b := mem_range.mpr (Nat.mod_lt L hbpos)
  have h := (hQ (L / b) hq (L % b) hr).le
  have heq : b * (L / b) + L % b = L := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod L b
  simpa only [heq] using h

theorem uniform_relative_lengths (b : ℕ) (hb : 3 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      |heightSum b L - wordMain b L| ≤ ε * wordMain b L := by
  obtain ⟨L₀, hL₀, hratio⟩ := uniform_ratio_lengths b hb ε hε
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL
  have hw := wordMain_pos b L hb (by omega)
  have hr := hratio L hL
  have heq : heightSum b L / wordMain b L - 1 = (heightSum b L - wordMain b L) / wordMain b L := by
    field_simp
  rw [heq, abs_div, abs_of_pos hw] at hr
  exact (div_le_iff₀ hw).mp hr

theorem uniform_critical_relative (C : ℝ) (b : ℕ) (hb : 3 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |heightSum b L - wordMain b L| ≤ ε * wordMain b L := by
  obtain ⟨L₀, _hL₀, hrelative⟩ := uniform_relative_lengths b hb ε hε
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C (L₀ + 1)
  refine ⟨max 2 NG, by omega, ?_⟩
  intro N hN L hband
  have hlarge := (hgeom N (by omega) L hband).2.1
  exact hrelative L (by omega)

end PaperP1.ChannelWordPhase
