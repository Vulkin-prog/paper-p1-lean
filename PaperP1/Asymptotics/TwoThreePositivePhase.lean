module

public import PaperP1.Arithmetic.TwoThreePositiveParity
public import PaperP1.Asymptotics.OneTwoChannelPhase

/-! # Uniform positive two-to-three phase, without fixing a residue

All three finite residue limits are assembled before the length is chosen.
The positive phase is indexed by B=L+1, as in the original dyadic profile.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoThreePositivePhase

open Finset Filter PaperP1.ChannelSumIdentity PaperP1.TwoThreePositiveParity

def positiveMain (L : ℕ) : ℝ :=
  ((3 : ℝ) + ((L + 1) % 3 : ℕ)) / 6 * ((L + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((L + 1) / 3)

theorem positiveMain_pos (L : ℕ) : 0 < positiveMain L := by unfold positiveMain; positivity

theorem positive_normalized_identity {k r : ℕ} (hk : 2 ≤ k) (hr : r < 3) :
    (unsigned (3 * k + r - 1) 2 3 : ℝ) / ((k : ℝ) * (2 : ℝ) ^ k) =
      ((3 : ℝ) + r) / 2 + (((r : ℝ) ^ 2 + 5 * r + 18) / 2) * (k : ℝ)⁻¹ -
        15 * (1 / 2 : ℝ) ^ k - (5 * (r : ℝ) + 6) * ((k : ℝ)⁻¹ * (1 / 2 : ℝ) ^ k) := by
  rw [unsigned_formula hk hr]
  push_cast
  have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hp : (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k / 2 := by
    have heq : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    rw [heq]
    ring
  have hg : (1 / 2 : ℝ) ^ k = 1 / (2 : ℝ) ^ k := by rw [div_pow, one_pow]
  rw [hp, hg]
  field_simp
  ring

theorem tendsto_positive_normalized (r : ℕ) (hr : r < 3) :
    Tendsto (fun k : ℕ ↦ (unsigned (3 * k + r - 1) 2 3 : ℝ) / ((k : ℝ) * (2 : ℝ) ^ k))
      atTop (nhds (((3 : ℝ) + r) / 2)) := by
  have hi : Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht := (((tendsto_const_nhds (x := ((3 : ℝ) + r) / 2)).add
    (hi.const_mul (((r : ℝ) ^ 2 + 5 * r + 18) / 2))).sub (hg.const_mul 15)).sub
      ((hi.mul hg).const_mul (5 * (r : ℝ) + 6))
  have ht' : Tendsto (fun k : ℕ ↦ ((3 : ℝ) + r) / 2 +
      (((r : ℝ) ^ 2 + 5 * r + 18) / 2) * (k : ℝ)⁻¹ - 15 * (1 / 2 : ℝ) ^ k -
      (5 * (r : ℝ) + 6) * ((k : ℝ)⁻¹ * (1 / 2 : ℝ) ^ k)) atTop
      (nhds (((3 : ℝ) + r) / 2)) := by
    simpa only [mul_zero, add_zero, sub_zero] using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 2] with k hk
  exact (positive_normalized_identity hk hr).symm

theorem positiveMain_eval {k r : ℕ} (hk : 1 ≤ k) (hr : r < 3) :
    positiveMain (3 * k + r - 1) = ((3 : ℝ) + r) / 6 * ((3 * k + r : ℕ) : ℝ) * (2 : ℝ) ^ k := by
  have hB : (3 * k + r - 1) + 1 = 3 * k + r := by omega
  have hmod : (3 * k + r) % 3 = r := by omega
  have hdiv : (3 * k + r) / 3 = k := by omega
  rw [positiveMain, hB, hmod, hdiv]

theorem tendsto_positiveMain_normalized (r : ℕ) (hr : r < 3) :
    Tendsto (fun k : ℕ ↦ positiveMain (3 * k + r - 1) / ((k : ℝ) * (2 : ℝ) ^ k))
      atTop (nhds (((3 : ℝ) + r) / 2)) := by
  have hi : Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := ((hi.const_mul (r : ℝ)).const_add 3).const_mul (((3 : ℝ) + r) / 6)
  have ht' : Tendsto (fun k : ℕ ↦ (((3 : ℝ) + r) / 6) * (3 + (r : ℝ) * (k : ℝ)⁻¹))
      atTop (nhds (((3 : ℝ) + r) / 2)) := by
    simpa only [mul_zero, add_zero, show (((3 : ℝ) + r) / 6) * 3 = ((3 : ℝ) + r) / 2 by ring] using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [positiveMain_eval hk hr]
  have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  push_cast
  field_simp

theorem tendsto_positive_ratio (r : ℕ) (hr : r < 3) :
    Tendsto (fun k : ℕ ↦ (unsigned (3 * k + r - 1) 2 3 : ℝ) / positiveMain (3 * k + r - 1))
      atTop (nhds 1) :=
  PaperP1.OneTwoChannelPhase.ratio_of_normalized (by positivity : ((3 : ℝ) + r) / 2 ≠ 0)
    (tendsto_positive_normalized r hr) (tendsto_positiveMain_normalized r hr)

theorem uniform_ratio_lengths (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      |(unsigned L 2 3 : ℝ) / positiveMain L - 1| ≤ ε := by
  have he (r : ℕ) (hr : r ∈ range 3) : ∀ᶠ q : ℕ in atTop,
      |(unsigned (3 * q + r - 1) 2 3 : ℝ) / positiveMain (3 * q + r - 1) - 1| < ε := by
    have hpos := ((tendsto_positive_ratio r (mem_range.mp hr)).sub
      (tendsto_const_nhds (x := (1 : ℝ)))).abs
    have hpos' : Tendsto (fun q : ℕ ↦
        |(unsigned (3 * q + r - 1) 2 3 : ℝ) / positiveMain (3 * q + r - 1) - 1|)
        atTop (nhds 0) := by simpa only [sub_self, abs_zero] using hpos
    exact hpos'.eventually (eventually_lt_nhds hε)
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp ((Finset.eventually_all (range 3)).mpr he)
  refine ⟨3 * (Q + 2), by omega, ?_⟩
  intro L hL
  have hpos := (hQ ((L + 1) / 3) (by omega) ((L + 1) % 3)
    (mem_range.mpr (Nat.mod_lt _ (by omega : 0 < 3)))).le
  have hp : 3 * ((L + 1) / 3) + (L + 1) % 3 - 1 = L := by omega
  simpa only [hp] using hpos

theorem uniform_relative_lengths (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      |(unsigned L 2 3 : ℝ) - positiveMain L| ≤ ε * positiveMain L := by
  obtain ⟨L₀, hL₀, h⟩ := uniform_ratio_lengths ε hε
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL
  have hp := h L hL
  have hpos := positiveMain_pos L
  have heq : (unsigned L 2 3 : ℝ) / positiveMain L - 1 =
      ((unsigned L 2 3 : ℝ) - positiveMain L) / positiveMain L := by field_simp
  rw [heq, abs_div, abs_of_pos hpos] at hp
  exact (div_le_iff₀ hpos).mp hp

theorem uniform_critical_relative (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |(unsigned L 2 3 : ℝ) - positiveMain L| ≤ ε * positiveMain L := by
  obtain ⟨L₀, _hL₀, h⟩ := uniform_relative_lengths ε hε
  obtain ⟨N₀, hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C (L₀ + 1)
  refine ⟨N₀, ?_⟩
  intro N hN L hcrit
  have hh := (hG N (by omega) L hcrit).2.1
  exact h L (by omega)

end PaperP1.TwoThreePositivePhase
