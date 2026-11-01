module

public import PaperP1.Asymptotics.PrimeCylinderScale
public import PaperP1.Model.RegularSetAsymptotic
public import PaperP1.Model.LatePrimeWindows

/-! # The actual regular compatible population has size asymptotic to N/(2q) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LatePrimePopulation

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrimeCylinderScale PaperP1.LatePrimeStarts

def population (q : ℕ) : Finset ℕ :=
  starts (size q) q ∩ RegularStarts.regularStarts (size q) (q - 1)

theorem population_subset (q : ℕ) : population q ⊆ starts (size q) q := inter_subset_left

theorem population_regular (q : ℕ) : population q ⊆ RegularStarts.regularStarts (size q) (q - 1) :=
  inter_subset_right

theorem population_positive {q : ℕ} (hq : Nat.Prime q) {A : Finset ℕ} (hA : A ⊆ population q) :
    0 < infiniteJointMoment (q - 1) A :=
  LatePrimeWindows.joint_positive hq (hA.trans (population_subset q))

theorem population_no_good_pair {q : ℕ} (hq : 2 ≤ q) {H : ℝ} {e : Finset ℕ}
    (he : e ∈ GoodEdgeCompression.goodEdges H (size q) (q - 1)) : ¬e ⊆ population q := by
  intro hsub
  exact LatePrimeWindows.no_good_pair hq he (hsub.trans (population_subset q))

theorem critical_band (q : ℕ) :
    |((q - 1 : ℕ) : ℝ) - Real.log (size q) / Real.log 2| ≤ 0 := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [log_size]
  have heq : ((q - 1 : ℕ) : ℝ) * Real.log 2 / Real.log 2 = ((q - 1 : ℕ) : ℝ) := by field_simp
  rw [heq, sub_self, abs_zero]

theorem all_starts_ratio :
    Tendsto (fun q : ℕ ↦ ((starts (size q) q).card : ℝ) * q / size q) atTop (nhds (1 / 2 : ℝ)) := by
  have hqInv : Tendsto (fun q : ℕ ↦ (4 : ℝ) / q) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlo : Tendsto (fun q : ℕ ↦ (1 / 2 : ℝ) - 4 / q - 8 * ((q : ℝ) / size q))
      atTop (nhds (1 / 2 : ℝ)) := by
    simpa only [sub_zero, mul_zero] using
      (tendsto_const_nhds.sub hqInv).sub (index_div_size_tendsto.const_mul 8)
  have hhi : Tendsto (fun q : ℕ ↦ (1 / 2 : ℝ) + (q : ℝ) / size q)
      atTop (nhds (1 / 2 : ℝ)) := by simpa using tendsto_const_nhds.add index_div_size_tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop 1] with q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hn : (0 : ℝ) < size q := by exact_mod_cast size_pos q
    have h := mul_le_mul_of_nonneg_right (card_bounds (N := size q) (by omega : 0 < q)).1
      (div_nonneg hq0.le hn.le)
    have heq : ((size q : ℝ) / (2 * q) - 4 * size q / (q : ℝ) ^ 2 - 8) *
        ((q : ℝ) / size q) = 1 / 2 - 4 / q - 8 * ((q : ℝ) / size q) := by field_simp
    rw [heq] at h
    simpa only [mul_div_assoc] using h
  · filter_upwards [eventually_ge_atTop 1] with q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hn : (0 : ℝ) < size q := by exact_mod_cast size_pos q
    have h := mul_le_mul_of_nonneg_right (card_bounds (N := size q) (by omega : 0 < q)).2
      (div_nonneg hq0.le hn.le)
    have heq : ((size q : ℝ) / (2 * q) + 1) * ((q : ℝ) / size q) = 1 / 2 + (q : ℝ) / size q := by
      field_simp
    rw [heq] at h
    simpa only [mul_div_assoc] using h

theorem sqrt_error_tendsto :
    Tendsto (fun q : ℕ ↦ (size q : ℝ) ^ (1 / 2 : ℝ) * q / size q) atTop (nhds 0) := by
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hindex : Tendsto (fun q : ℕ ↦ (q : ℝ) / Real.log (size q)) atTop (nhds (Real.log 2)⁻¹) := by
    simpa only [inv_div] using log_size_div_index_tendsto.inv₀ hlog2
  have hsmall : Tendsto (fun q : ℕ ↦ Real.log (size q) / (size q : ℝ) ^ (1 / 2 : ℝ))
      atTop (nhds 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (PNT.tendsto_pow_log_div_pow_atTop (1 / 2) 1 (by norm_num)).comp size_real_tendsto
  have heq : (fun q : ℕ ↦ (size q : ℝ) ^ (1 / 2 : ℝ) * q / size q) =ᶠ[atTop]
      (fun q : ℕ ↦ ((q : ℝ) / Real.log (size q)) *
        (Real.log (size q) / (size q : ℝ) ^ (1 / 2 : ℝ))) := by
    filter_upwards [eventually_ge_atTop 2] with q hq
    have hn : (0 : ℝ) < size q := by exact_mod_cast size_pos q
    have hN2 : 1 < size q := by have h := index_le_size (by omega : 1 ≤ q); omega
    have hlog : Real.log (size q) ≠ 0 := (Real.log_pos (by exact_mod_cast hN2)).ne'
    have hp : 0 < (size q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
    have hpow : (size q : ℝ) ^ (1 / 2 : ℝ) * (size q : ℝ) ^ (1 / 2 : ℝ) = size q := by
      rw [← Real.rpow_add hn]
      norm_num
    calc
      _ = (q : ℝ) / (size q : ℝ) ^ (1 / 2 : ℝ) := by
        apply (div_eq_div_iff hn.ne' hp.ne').mpr
        calc
          _ = (q : ℝ) * ((size q : ℝ) ^ (1 / 2 : ℝ) * (size q : ℝ) ^ (1 / 2 : ℝ)) := by ring
          _ = _ := by rw [hpow]
      _ = _ := by field_simp
  exact Tendsto.congr' heq.symm (by simpa only [mul_zero] using hindex.mul hsmall)

theorem population_card_loss {q : ℕ} (hq : 2 ≤ q) :
    (starts (size q) q).card ≤ (population q).card +
      (RegularStarts.irregularStarts (size q) (q - 1)).card := by
  classical
  have hcover : starts (size q) q ⊆ population q ∪ RegularStarts.irregularStarts (size q) (q - 1) := by
    intro x hx
    by_cases hreg : x ∈ RegularStarts.regularStarts (size q) (q - 1)
    · exact mem_union_left _ (mem_inter.mpr ⟨hx, hreg⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨starts_subset hq hx, hreg⟩)
  exact (card_le_card hcover).trans (card_union_le _ _)

theorem population_ratio :
    Tendsto (fun q : ℕ ↦ ((population q).card : ℝ) * q / size q) atTop (nhds (1 / 2 : ℝ)) := by
  have hlo : Tendsto (fun q : ℕ ↦ ((starts (size q) q).card : ℝ) * q / size q -
      (size q : ℝ) ^ (1 / 2 : ℝ) * q / size q) atTop (nhds (1 / 2 : ℝ)) := by
    simpa only [sub_zero] using all_starts_ratio.sub sqrt_error_tendsto
  obtain ⟨N₀, hN₀⟩ := RegularSetAsymptotic.irregular_count_critical 0 (1 / 2) (by norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo all_starts_ratio
  · filter_upwards [eventually_ge_atTop 2, size_tendsto.eventually (eventually_ge_atTop N₀)] with q hq hN
    have hcount := hN₀ (size q) hN (q - 1) (critical_band q)
    have hloss : ((starts (size q) q).card : ℝ) ≤ (population q).card +
        (RegularStarts.irregularStarts (size q) (q - 1)).card := by exact_mod_cast population_card_loss hq
    have hbase : ((starts (size q) q).card : ℝ) - (size q : ℝ) ^ (1 / 2 : ℝ) ≤ (population q).card := by linarith
    have hmul := mul_le_mul_of_nonneg_right hbase (show 0 ≤ (q : ℝ) / size q by positivity)
    simpa only [sub_mul, mul_div_assoc] using hmul
  · filter_upwards [] with q
    have hcard : ((population q).card : ℝ) ≤ (starts (size q) q).card := by exact_mod_cast card_le_card (population_subset q)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg q)) (Nat.cast_nonneg (size q))

theorem population_nonempty_eventually : ∀ᶠ q : ℕ in atTop, (population q).Nonempty := by
  have hpos := population_ratio.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hpos] with q hq
  apply card_pos.mp
  by_contra h
  have hz : (population q).card = 0 := by omega
  simp only [hz, Nat.cast_zero, zero_mul, zero_div] at hq
  exact (lt_irrefl (0 : ℝ)) hq

end PaperP1.LatePrimePopulation
