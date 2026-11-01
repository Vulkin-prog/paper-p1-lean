module

public import PaperP1.Model.LargeBoundaryMass
public import PaperP1.Asymptotics.RetainedClassTheorem
public import PaperP1.Asymptotics.CriticalChannelPowers

/-! # Companion T12.2: the actual large-boundary mass is O(N^(-3/2)) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargeBoundaryTail

open Filter Finset PaperP1.Arithmetic PaperP1.LargeBoundaryMass

theorem critical_parameters (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 2 ≤ N ∧ 7 ≤ L := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop ((C + 7) * Real.log 2)))
  refine ⟨max 2 Nl, ?_⟩
  intro N hN L hband
  have hlower : C + 7 ≤ Real.log N / Real.log 2 := (le_div_iff₀ hlog2).mpr (hNl N (by omega))
  have hLreal : (7 : ℝ) ≤ L := by linarith [(abs_le.mp hband).1]
  exact ⟨by omega, by exact_mod_cast hLreal⟩

theorem critical_power_bound {N L : ℕ} {C : ℝ} (a : ℝ) (ha : 0 ≤ a) (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    (2 : ℝ) ^ (a * (L : ℝ)) ≤ (2 : ℝ) ^ (a * C) * (N : ℝ) ^ a := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhigh : (L : ℝ) ≤ Real.log N / Real.log 2 + C := by linarith [(abs_le.mp hband).2]
  have hmul := mul_le_mul_of_nonneg_right hhigh hlog2.le
  rw [add_mul, div_mul_cancel₀ _ hlog2.ne'] at hmul
  have hscaled := mul_le_mul_of_nonneg_left hmul ha
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hn, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert hscaled using 1 <;> ring

theorem critical_prefactor {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    (2 : ℝ) ^ (3 * (L : ℝ) / 2) ≤ (2 : ℝ) ^ (3 * C / 2) * (N : ℝ) ^ (3 / 2 : ℝ) := by
  simpa only [div_mul_eq_mul_div] using critical_power_bound (3 / 2 : ℝ) (by norm_num) hN hband

theorem regular_mean_bound {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    ((PaperP1.RegularStarts.regularStarts N L).card : ℝ) * nominal L ≤ (2 : ℝ) ^ C := by
  have hcard : (PaperP1.RegularStarts.regularStarts N L).card ≤ N := by
    have h := card_le_card (PaperP1.RegularStarts.regularStarts_subset N L)
    simpa only [PaperP1.Model.dyadicBlock, Nat.card_Ico, two_mul, Nat.add_sub_cancel_left] using h
  have hp := PaperP1.LocalRigidityConsequences.nominal_marginal_bound hN hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (N : ℝ) * nominal L := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by unfold nominal; positivity)
    _ ≤ (N : ℝ) * ((2 : ℝ) ^ C / N) := mul_le_mul_of_nonneg_left hp hn.le
    _ = _ := by field_simp

theorem mass_nonneg (H : ℝ) (N L K : ℕ) : 0 ≤ mass H N L K := by
  apply sum_nonneg
  intro I _
  exact mul_nonneg (by positivity) (PaperP1.Model.InfiniteStarts.infiniteJointMoment_nonneg L I)

theorem critical_mass_bound {H : ℝ} {N L : ℕ} {C : ℝ} (hN : 2 ≤ N) (hL : 7 ≤ L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (hmean : ((PaperP1.RegularStarts.regularStarts N L).card : ℝ) * nominal L ≤ Λ) :
    mass H N L (PaperP1.BoundaryCutoff.cutoff Λ hΛ N) ≤
      (2 : ℝ) ^ (3 * C / 2) * (N : ℝ) ^ (-3 / 2 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (2 : ℝ) ^ (3 * (L : ℝ) / 2) * (N : ℝ) ^ (-3 : ℝ) := cutoff_mass_bound hN hL Λ hΛ hmean
    _ ≤ ((2 : ℝ) ^ (3 * C / 2) * (N : ℝ) ^ (3 / 2 : ℝ)) * (N : ℝ) ^ (-3 : ℝ) :=
      mul_le_mul_of_nonneg_right (critical_prefactor hN hband) (Real.rpow_nonneg hn.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hn]
      norm_num

theorem companion_T12_2_with_mean_bound (C Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ((PaperP1.RegularStarts.regularStarts N L).card : ℝ) * nominal L ≤ Λ → ∀ H : ℝ,
          mass H N L (PaperP1.BoundaryCutoff.cutoff Λ hΛ N) ≤
            (2 : ℝ) ^ (3 * C / 2) * (N : ℝ) ^ (-3 / 2 : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := critical_parameters C
  refine ⟨N₀, ?_⟩
  intro N hN L hband hmean H
  have hp := hN₀ N hN L hband
  exact critical_mass_bound hp.1 hp.2 hband Λ hΛ hmean

theorem companion_T12_2 (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
        mass H N L (PaperP1.BoundaryCutoff.cutoff ((2 : ℝ) ^ C) (Real.rpow_pos_of_pos (by norm_num) C) N) ≤
          (2 : ℝ) ^ (3 * C / 2) * (N : ℝ) ^ (-3 / 2 : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := companion_T12_2_with_mean_bound C ((2 : ℝ) ^ C) (Real.rpow_pos_of_pos (by norm_num) C)
  refine ⟨max 2 N₀, ?_⟩
  intro N hN L hband H
  exact hN₀ N (by omega) L hband (regular_mean_bound (by omega) hband) H

theorem improved_critical_mass_bound {H : ℝ} {N L : ℕ} {C : ℝ} (hN : 2 ≤ N) (hL : 7 ≤ L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (hmean : ((PaperP1.RegularStarts.regularStarts N L).card : ℝ) * nominal L ≤ Λ) :
    mass H N L (PaperP1.BoundaryCutoff.cutoff Λ hΛ N) ≤
      (2 * (2 : ℝ) ^ (4 * C / 3)) * (N : ℝ) ^ (-5 / 3 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : (2 : ℝ) ^ (4 * (L : ℝ) / 3) ≤ (2 : ℝ) ^ (4 * C / 3) * (N : ℝ) ^ (4 / 3 : ℝ) := by
    simpa only [div_mul_eq_mul_div] using critical_power_bound (4 / 3 : ℝ) (by norm_num) hN hband
  have hpref : (2 : ℝ) ^ (4 * (L : ℝ) / 3 + 1) ≤
      (2 * (2 : ℝ) ^ (4 * C / 3)) * (N : ℝ) ^ (4 / 3 : ℝ) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
    convert hm using 1 <;> ring
  calc
    _ ≤ (2 : ℝ) ^ (4 * (L : ℝ) / 3 + 1) * (N : ℝ) ^ (-3 : ℝ) := precise_cutoff_mass_bound hN hL Λ hΛ hmean
    _ ≤ ((2 * (2 : ℝ) ^ (4 * C / 3)) * (N : ℝ) ^ (4 / 3 : ℝ)) * (N : ℝ) ^ (-3 : ℝ) :=
      mul_le_mul_of_nonneg_right hpref (Real.rpow_nonneg hn.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hn]
      norm_num

theorem improved_source_tail (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
        mass H N L (PaperP1.BoundaryCutoff.cutoff ((2 : ℝ) ^ C) (Real.rpow_pos_of_pos (by norm_num) C) N) ≤
          (2 * (2 : ℝ) ^ (4 * C / 3)) * (N : ℝ) ^ (-5 / 3 : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := critical_parameters C
  refine ⟨N₀, ?_⟩
  intro N hN L hband H
  have hp := hN₀ N hN L hband
  exact improved_critical_mass_bound hp.1 hp.2 hband ((2 : ℝ) ^ C)
    (Real.rpow_pos_of_pos (by norm_num) C) (regular_mean_bound hp.1 hband)

end PaperP1.LargeBoundaryTail
