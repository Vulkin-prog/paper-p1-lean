module

public import PaperP1.Arithmetic.ThreeSlopePrivatePopulation
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Asymptotics.LogarithmicWordPowers
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # A positive linear density of actual private rational triple witnesses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeSlopePrivateDensity

open PaperP1.Arithmetic PaperP1.Model PaperP1.ThreeSlopePrivatePopulation
  PaperP1.ThreeSlopeProgressions PaperP1.PrivateNormalizedFamilies PaperP1.CriticalBandScale

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem bad_rate (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1000 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((bad N L).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨ND, hd⟩ := GlobalDefectCount.global_defect_count_le_rpow_eventually 66
    (10 * upperScale) (by norm_num) (mul_nonneg (by norm_num) upperScale_pos.le) (ε / 2) (by positivity)
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually upperScale
    upperScale_pos.le 3 1 (ε / 2) (by positivity)
  refine ⟨max 1000 (max NG (max ND NP)), by omega, ?_⟩
  intro N hN L hband
  obtain ⟨_hN2, _hBmin, _hBtwo, hthin, _hBlo, hBhi⟩ := hg N (by omega) L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hH : ((10 * (L + 1) : ℕ) : ℝ) ≤ (10 * upperScale) * Real.log N := by
    push_cast at hBhi ⊢
    nlinarith only [hBhi]
  have hdef := hd N (by omega) (10 * (L + 1)) (66 * N) hH (by push_cast; exact le_rfl)
  have hfactor : 3 * ((L + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    have hh := hp N (by omega) L hBhi
    simpa only [pow_one, Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * (L + 1 : ℝ))] using hh
  calc
    _ ≤ 3 * ((L + 1 : ℕ) : ℝ) * (GlobalDefectCount.positiveDefectsBelow (10 * (L + 1)) (66 * N)).card := by
      exact_mod_cast bad_card (by omega) (by omega : L ≤ N)
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 / 2 + ε / 2) :=
      mul_le_mul hfactor hdef (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem linear_good_population (C : ℝ) :
    ∃ N₀ : ℕ, 1000 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      60 ≤ L ∧ (N : ℝ) / 120 ≤ ((good N L).card : ℝ) ∧
      ∀ t ∈ good N L, 1 ≤ t ∧ (∀ i, centres t i ∈ dyadicBlock N) ∧
        FiniteEvenSquareClasses.Private (valueUnion step (centres t) L) := by
  obtain ⟨NB, _hNB, hb⟩ := bad_rate C (1 / 4) (by norm_num)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 120 (3 / 4) (1 / 4) (by norm_num)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 61
  refine ⟨max 1000 (max NB (max NA NG)), by omega, ?_⟩
  intro N hN L hband
  have hwidth := (hg N (by omega) L hband).2.1
  have hbad : ((bad N L).card : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
    simpa only [show (1 / 2 : ℝ) + 1 / 4 = 3 / 4 by norm_num] using hb N (by omega) L hband
  have hsmall : 120 * (N : ℝ) ^ (3 / 4 : ℝ) ≤ N := by
    have hh := ha N (by omega)
    simpa only [show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, Real.rpow_one] using hh
  have hpop := parameter_count (by omega : 1000 ≤ N)
  have hpart : ((good N L).card : ℝ) + (bad N L).card = (parameters N).card := by
    exact_mod_cast good_bad_partition N L
  refine ⟨by omega, by linarith only [hbad, hsmall, hpop, hpart], ?_⟩
  intro t ht
  have hdata := Finset.mem_filter.mp ht
  exact ⟨(parameter_bounds (by omega) hdata.1).1, centres_dyadic (by omega) hdata.1, hdata.2.private⟩

end PaperP1.ThreeSlopePrivateDensity
