module

public import PaperP1.Arithmetic.OneTwoChannelParity
public import PaperP1.Asymptotics.SignedChannelPhaseLimit
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import Mathlib.Order.Filter.Finite

/-! # Distinct moving positive and signed phases at height two

The positive phase uses B=L+1 modulo two. The signed phase uses L modulo
two. Finite-residue limits will be assembled before choosing a critical
length; no residue is fixed in the uniform conclusion.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OneTwoChannelPhase

open Finset Filter PaperP1.ChannelSumIdentity PaperP1.OneTwoChannelParity

def positiveMain (L : ℕ) : ℝ :=
  ((2 : ℝ) + ((L + 1) % 2 : ℕ)) / 4 * ((L + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((L + 1) / 2)

def signedMain (L : ℕ) : ℝ :=
  (((L % 2 : ℕ) : ℝ) + 1) / 4 * (L : ℝ) * (2 : ℝ) ^ (L / 2)

theorem positiveMain_pos (L : ℕ) : 0 < positiveMain L := by unfold positiveMain; positivity

theorem signedMain_pos {L : ℕ} (hL : 0 < L) : 0 < signedMain L := by unfold signedMain; positivity

theorem positive_normalized_identity {k r : ℕ} (hk : 2 ≤ k) (hr : r < 2) :
    (unsigned (2 * k + r - 1) 1 2 : ℝ) / ((k : ℝ) * (2 : ℝ) ^ k) =
      ((2 : ℝ) + r) / 2 + ((6 + 4 * (r : ℝ)) / 2) * (k : ℝ)⁻¹ -
        6 * (1 / 2 : ℝ) ^ k - (3 * (r : ℝ) + 2) * ((k : ℝ)⁻¹ * (1 / 2 : ℝ) ^ k) := by
  rw [unsigned_formula hk hr]
  push_cast
  have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hp : (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k / 2 := by
    have heq : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    rw [heq]
    ring
  have hg : (1 / 2 : ℝ) ^ k = 1 / (2 : ℝ) ^ k := by rw [div_pow, one_pow]
  rw [hp, hg]
  field_simp
  ring

theorem tendsto_positive_normalized (r : ℕ) (hr : r < 2) :
    Tendsto (fun k : ℕ ↦ (unsigned (2 * k + r - 1) 1 2 : ℝ) / ((k : ℝ) * (2 : ℝ) ^ k))
      atTop (nhds (((2 : ℝ) + r) / 2)) := by
  have hi : Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht := (((tendsto_const_nhds (x := ((2 : ℝ) + r) / 2)).add
    (hi.const_mul ((6 + 4 * (r : ℝ)) / 2))).sub (hg.const_mul 6)).sub
      ((hi.mul hg).const_mul (3 * (r : ℝ) + 2))
  have ht' : Tendsto (fun k : ℕ ↦ ((2 : ℝ) + r) / 2 + ((6 + 4 * (r : ℝ)) / 2) * (k : ℝ)⁻¹ -
      6 * (1 / 2 : ℝ) ^ k - (3 * (r : ℝ) + 2) * ((k : ℝ)⁻¹ * (1 / 2 : ℝ) ^ k)) atTop
      (nhds (((2 : ℝ) + r) / 2)) := by
    simpa only [mul_zero, add_zero, sub_zero] using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 2] with k hk
  exact (positive_normalized_identity hk hr).symm

theorem tendsto_signed_normalized (s : ℕ) (hs : s < 2) :
    Tendsto (fun m : ℕ ↦ (signed (2 * m + s) 1 2 : ℝ) / ((m : ℝ) * (2 : ℝ) ^ m))
      atTop (nhds (((s : ℝ) + 1) / 2)) := by
  have hh := PaperP1.SignedChannelPhaseLimit.tendsto_normalized 1 2 s hs
  simpa only [PaperP1.SignedChannelPhaseLimit.linearTerm, Nat.cast_ofNat, Nat.cast_one,
    show ((2 : ℝ) - 1) * (2 + (s : ℝ) - 1) = (s : ℝ) + 1 by ring] using hh

theorem positiveMain_eval {k r : ℕ} (hk : 1 ≤ k) (hr : r < 2) :
    positiveMain (2 * k + r - 1) = ((2 : ℝ) + r) / 4 * ((2 * k + r : ℕ) : ℝ) * (2 : ℝ) ^ k := by
  have hB : (2 * k + r - 1) + 1 = 2 * k + r := by omega
  have hmod : (2 * k + r) % 2 = r := by omega
  have hdiv : (2 * k + r) / 2 = k := by omega
  rw [positiveMain, hB, hmod, hdiv]

theorem signedMain_eval {m s : ℕ} (hs : s < 2) :
    signedMain (2 * m + s) = ((s : ℝ) + 1) / 4 * ((2 * m + s : ℕ) : ℝ) * (2 : ℝ) ^ m := by
  have hmod : (2 * m + s) % 2 = s := by omega
  have hdiv : (2 * m + s) / 2 = m := by omega
  rw [signedMain, hmod, hdiv]

theorem tendsto_positiveMain_normalized (r : ℕ) (hr : r < 2) :
    Tendsto (fun k : ℕ ↦ positiveMain (2 * k + r - 1) / ((k : ℝ) * (2 : ℝ) ^ k))
      atTop (nhds (((2 : ℝ) + r) / 2)) := by
  have hi : Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := ((hi.const_mul (r : ℝ)).const_add 2).const_mul (((2 : ℝ) + r) / 4)
  have ht' : Tendsto (fun k : ℕ ↦ (((2 : ℝ) + r) / 4) * (2 + (r : ℝ) * (k : ℝ)⁻¹))
      atTop (nhds (((2 : ℝ) + r) / 2)) := by
    simpa only [mul_zero, add_zero, show (((2 : ℝ) + r) / 4) * 2 = ((2 : ℝ) + r) / 2 by ring] using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [positiveMain_eval hk hr]
  have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  push_cast
  field_simp

theorem tendsto_signedMain_normalized (s : ℕ) (hs : s < 2) :
    Tendsto (fun m : ℕ ↦ signedMain (2 * m + s) / ((m : ℝ) * (2 : ℝ) ^ m))
      atTop (nhds (((s : ℝ) + 1) / 2)) := by
  have hi : Tendsto (fun m : ℕ ↦ (m : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := ((hi.const_mul (s : ℝ)).const_add 2).const_mul (((s : ℝ) + 1) / 4)
  have ht' : Tendsto (fun m : ℕ ↦ (((s : ℝ) + 1) / 4) * (2 + (s : ℝ) * (m : ℝ)⁻¹))
      atTop (nhds (((s : ℝ) + 1) / 2)) := by
    simpa only [mul_zero, add_zero, show (((s : ℝ) + 1) / 4) * 2 = ((s : ℝ) + 1) / 2 by ring] using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [signedMain_eval hs]
  have hmn : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  push_cast
  field_simp


theorem ratio_of_normalized {f g : ℕ → ℝ} {a : ℝ} (ha : a ≠ 0)
    (hf : Tendsto (fun q : ℕ ↦ f q / ((q : ℝ) * (2 : ℝ) ^ q)) atTop (nhds a))
    (hg : Tendsto (fun q : ℕ ↦ g q / ((q : ℝ) * (2 : ℝ) ^ q)) atTop (nhds a)) :
    Tendsto (fun q : ℕ ↦ f q / g q) atTop (nhds 1) := by
  have ht := hf.div hg ha
  have ht' : Tendsto (fun q : ℕ ↦ (f q / ((q : ℝ) * (2 : ℝ) ^ q)) /
      (g q / ((q : ℝ) * (2 : ℝ) ^ q))) atTop (nhds 1) := by
    change Tendsto (fun q : ℕ ↦ (f q / ((q : ℝ) * (2 : ℝ) ^ q)) /
      (g q / ((q : ℝ) * (2 : ℝ) ^ q))) atTop (nhds (a / a)) at ht
    simpa only [div_self ha] using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  exact div_div_div_cancel_right₀ (by positivity : (q : ℝ) * (2 : ℝ) ^ q ≠ 0) _ _

theorem tendsto_positive_ratio (r : ℕ) (hr : r < 2) :
    Tendsto (fun k : ℕ ↦ (unsigned (2 * k + r - 1) 1 2 : ℝ) / positiveMain (2 * k + r - 1))
      atTop (nhds 1) :=
  ratio_of_normalized (by positivity : ((2 : ℝ) + r) / 2 ≠ 0)
    (tendsto_positive_normalized r hr) (tendsto_positiveMain_normalized r hr)

theorem tendsto_signed_ratio (s : ℕ) (hs : s < 2) :
    Tendsto (fun m : ℕ ↦ (signed (2 * m + s) 1 2 : ℝ) / signedMain (2 * m + s)) atTop (nhds 1) :=
  ratio_of_normalized (by positivity : ((s : ℝ) + 1) / 2 ≠ 0)
    (tendsto_signed_normalized s hs) (tendsto_signedMain_normalized s hs)

theorem uniform_ratio_lengths (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      |(unsigned L 1 2 : ℝ) / positiveMain L - 1| ≤ ε ∧
      |(signed L 1 2 : ℝ) / signedMain L - 1| ≤ ε := by
  have he (r : ℕ) (hr : r ∈ range 2) : ∀ᶠ q : ℕ in atTop,
      |(unsigned (2 * q + r - 1) 1 2 : ℝ) / positiveMain (2 * q + r - 1) - 1| < ε ∧
      |(signed (2 * q + r) 1 2 : ℝ) / signedMain (2 * q + r) - 1| < ε := by
    have hr2 := mem_range.mp hr
    have hpos := ((tendsto_positive_ratio r hr2).sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
    have hsign := ((tendsto_signed_ratio r hr2).sub (tendsto_const_nhds (x := (1 : ℝ)))).abs
    have hpos' : Tendsto (fun q : ℕ ↦ |(unsigned (2 * q + r - 1) 1 2 : ℝ) / positiveMain (2 * q + r - 1) - 1|)
        atTop (nhds 0) := by simpa only [sub_self, abs_zero] using hpos
    have hsign' : Tendsto (fun q : ℕ ↦ |(signed (2 * q + r) 1 2 : ℝ) / signedMain (2 * q + r) - 1|)
        atTop (nhds 0) := by simpa only [sub_self, abs_zero] using hsign
    exact (hpos'.eventually (eventually_lt_nhds hε)).and (hsign'.eventually (eventually_lt_nhds hε))
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp ((Finset.eventually_all (range 2)).mpr he)
  refine ⟨2 * (Q + 2), by omega, ?_⟩
  intro L hL
  have hpos := (hQ ((L + 1) / 2) (by omega) ((L + 1) % 2) (mem_range.mpr (Nat.mod_lt _ (by omega : 0 < 2)))).1.le
  have hsign := (hQ (L / 2) (by omega) (L % 2) (mem_range.mpr (Nat.mod_lt _ (by omega : 0 < 2)))).2.le
  have hp : 2 * ((L + 1) / 2) + (L + 1) % 2 - 1 = L := by omega
  have hs : 2 * (L / 2) + L % 2 = L := by omega
  exact ⟨by simpa only [hp] using hpos, by simpa only [hs] using hsign⟩

theorem uniform_relative_lengths (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      |(unsigned L 1 2 : ℝ) - positiveMain L| ≤ ε * positiveMain L ∧
      |(signed L 1 2 : ℝ) - signedMain L| ≤ ε * signedMain L := by
  obtain ⟨L₀, hL₀, h⟩ := uniform_ratio_lengths ε hε
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL
  obtain ⟨hp, hs⟩ := h L hL
  have hpos := positiveMain_pos L
  have hsign := signedMain_pos (by omega : 0 < L)
  have heqp : (unsigned L 1 2 : ℝ) / positiveMain L - 1 = ((unsigned L 1 2 : ℝ) - positiveMain L) / positiveMain L := by field_simp
  have heqs : (signed L 1 2 : ℝ) / signedMain L - 1 = ((signed L 1 2 : ℝ) - signedMain L) / signedMain L := by field_simp
  rw [heqp, abs_div, abs_of_pos hpos] at hp
  rw [heqs, abs_div, abs_of_pos hsign] at hs
  exact ⟨(div_le_iff₀ hpos).mp hp, (div_le_iff₀ hsign).mp hs⟩

theorem uniform_critical_relative (C ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      |(unsigned L 1 2 : ℝ) - positiveMain L| ≤ ε * positiveMain L ∧
      |(signed L 1 2 : ℝ) - signedMain L| ≤ ε * signedMain L := by
  obtain ⟨L₀, _hL₀, h⟩ := uniform_relative_lengths ε hε
  obtain ⟨M₀, hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C (L₀ + 1)
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit
  have hh := (hG M (by omega) L hcrit).2.1
  exact h L (by omega)

end PaperP1.OneTwoChannelPhase
