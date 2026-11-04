module

public import PaperP1.Model.PositionalGroundCoupling
public import PaperP1.Probability.PositionalTargetExtension
public import PaperP1.Asymptotics.WeakPairIncidence
public import PaperP1.Model.RegularSetAsymptotic
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Original and reference fields both restore excluded positions at rate one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalRestorationRates

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CompletedPositionalLaw

theorem nominal_discarded_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ _x ∈ RegularStarts.irregularStarts N L, (2 ^ L : ℝ)⁻¹) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NI, hi⟩ := RegularSetAsymptotic.irregular_count_critical C (ε / 2) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ C) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NI + NA, by omega, ?_⟩
  intro N hN L hband
  calc
    _ = (2 ^ L : ℝ)⁻¹ * ((RegularStarts.irregularStarts N L).card : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ (2 ^ L : ℝ)⁻¹ * (N : ℝ) ^ (ε / 2) := mul_le_mul_of_nonneg_left (hi N (by omega) L hband) (by positivity)
    _ ≤ (2 : ℝ) ^ C * (N : ℝ) ^ (-1 + ε / 2) := RegularSetAsymptotic.nominal_times_rpow_bound (by omega) hband
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_actual_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ‖ofFinite (PositionalStoppedLaw.actualLaw (dyadicBlock N) L) -
        ofFinite (PositionalStoppedLaw.actualLaw (RegularStarts.regularStarts N L) L)‖ ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨ND, hd⟩ := RegularSetAsymptotic.discarded_activity_critical C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (4 * (2 : ℝ) ^ C) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + ND + NG + NA, by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  rw [← map_sub, norm_ofFinite]
  have hh := PositionalGroundCoupling.dyadic_disagreement_bound (N := N) (L := L)
    (RegularStarts.regularStarts N L) (dyadicBlock N)
    (RegularStarts.regularStarts_subset N L) Subset.rfl
  calc
    _ ≤ 2 * CountObservables.countDisagreement (dyadicBlock N) (RegularStarts.regularStarts N L) L := hh
    _ ≤ 2 * ((2 * (2 : ℝ) ^ C) * (N : ℝ) ^ (-1 + ε / 2)) :=
      mul_le_mul_of_nonneg_left (hd N (by omega) L hL hband) (by norm_num)
    _ = (4 * (2 : ℝ) ^ C) * (N : ℝ) ^ (-1 + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_target_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      let E := GoodEdgeCompression.goodEdges H N L
      ‖PositionalCompoundPoisson.target (dyadicBlock N) E (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L) -
        PositionalCompoundPoisson.target (RegularStarts.regularStarts N L) E
          (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)‖ ≤ (N : ℝ) ^ (-1 + ε) := by
  let δ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  obtain ⟨NS, _hNS, hs⟩ := nominal_discarded_mass C δ hδ
  obtain ⟨NP, _hNP, hp⟩ := WeakPairIncidence.full_single_rates_positive C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (2 * Real.exp 2) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NS + NP + NA, by omega, ?_⟩
  intro N hN L hband H
  dsimp only
  let G := RegularStarts.regularStarts N L
  let E := GoodEdgeCompression.goodEdges H N L
  let s := ∑ _x ∈ dyadicBlock N \ G, (2 ^ L : ℝ)⁻¹
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have heS : s = ∑ _x ∈ RegularStarts.irregularStarts N L, (2 ^ L : ℝ)⁻¹ := by
    dsimp only [s, G, RegularStarts.irregularStarts]
  have hS : s ≤ (N : ℝ) ^ (-1 + δ) := by rw [heS]; exact hs N (by omega) L hband
  have hS1 : s ≤ 1 := hS.trans ((Real.rpow_le_rpow_of_exponent_le hn1
    (by have hh := min_le_right (ε / 2) (1 / 2); dsimp only [δ]; linarith only [hh] : -1 + δ ≤ 0)).trans_eq
      (Real.rpow_zero N))
  have hSε : s ≤ (N : ℝ) ^ (-1 + ε / 2) := hS.trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by have hh := min_le_left (ε / 2) (1 / 2); dsimp only [δ]; linarith only [hh]))
  have hfinite := PositionalTargetExtension.restoration_bound G (dyadicBlock N) (RegularStarts.regularStarts_subset N L)
    E (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
    (fun e he ↦ RetainedGoodEdges.good_pair_regular (by omega) e he)
    (fun x _hx ↦ (hp N (by omega) L hband H x).le) (fun e _ ↦ infiniteJointMoment_nonneg L e)
    (fun _ _ ↦ by positivity)
  have hbound : 2 * s * Real.exp (2 * s) ≤ (2 * Real.exp 2) * (N : ℝ) ^ (-1 + ε / 2) := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hSε (by norm_num : (0 : ℝ) ≤ 2))
      (Real.exp_le_exp.mpr (by linarith only [hS1] : 2 * s ≤ 2)) (Real.exp_nonneg _) (by positivity)
    exact hh.trans_eq (by ring)
  calc
    _ ≤ 2 * s * Real.exp (2 * s) := by
      convert hfinite using 1; congr!
    _ ≤ (2 * Real.exp 2) * (N : ℝ) ^ (-1 + ε / 2) := hbound
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PositionalRestorationRates
