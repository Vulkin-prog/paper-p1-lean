module

public import PaperP1.Model.RegularSetAsymptotic
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Model.TripleRankGeometry

/-! # Uniform two-sided bounds for the actual original count mean -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalActualMean

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.RegularStarts

theorem mean_mono {N L : ℕ} {G H : Finset ℕ} (hGH : G ⊆ H) (hH : H ⊆ dyadicBlock N) :
    countMoment G L 1 ≤ countMoment H L 1 := by
  rw [countMoment_one (hGH.trans hH), countMoment_one hH]
  exact sum_le_sum_of_subset_of_nonneg hGH
    (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)

def lowerMean (C : ℝ) : ℝ := ((2 : ℝ) ^ C)⁻¹ / 2

theorem lowerMean_pos (C : ℝ) : 0 < lowerMean C := by unfold lowerMean; positivity

/-- The lower bound needs no unformalized curve-counting or pair-profile input. -/
theorem uniform_bounds (C : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      lowerMean C ≤ countMoment (dyadicBlock N) L 1 ∧
        countMoment (dyadicBlock N) L 1 ≤ 2 * (2 : ℝ) ^ C := by
  obtain ⟨NI, hirregular⟩ := RegularSetAsymptotic.irregular_count_critical C (1 / 2) (by norm_num)
  obtain ⟨NM, hmarg⟩ := TripleRankGeometry.critical_nominal_marginal_cap C
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 4 (max NI (max NM NG)), by omega, ?_⟩
  intro N hN L hband
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hi := hirregular N (by omega) L hband
  rw [← Real.sqrt_eq_rpow] at hi
  have hsqrt : Real.sqrt N ≤ (N : ℝ) / 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hcard : ((irregularStarts N L).card : ℝ) + (regularStarts N L).card = N := by
    exact_mod_cast RegularSetFinite.card_irregular_add_regular N L
  have hreg : (N : ℝ) / 2 ≤ (regularStarts N L).card := by linarith only [hi, hsqrt, hcard]
  constructor
  · calc
      _ = ((2 : ℝ) ^ C)⁻¹ / N * ((N : ℝ) / 2) := by unfold lowerMean; field_simp
      _ ≤ (2 ^ L : ℝ)⁻¹ * (regularStarts N L).card :=
        mul_le_mul (CriticalChannelPowers.nominal_lower hNtwo hband) hreg
          (by positivity) (by positivity)
      _ = countMoment (regularStarts N L) L 1 := (RegularSetFinite.mean_regular hNtwo hL).symm
      _ ≤ _ := mean_mono (regularStarts_subset N L) (subset_refl _)
  · rw [countMoment_one (subset_refl _)]
    calc
      _ ≤ ∑ _x ∈ dyadicBlock N, 2 * (2 ^ L : ℝ)⁻¹ :=
        sum_le_sum (fun x hx ↦ hmarg N (by omega) L hband x hx)
      _ = (N : ℝ) * (2 * (2 ^ L : ℝ)⁻¹) := by rw [sum_const, nsmul_eq_mul, dyadicBlock_card]
      _ ≤ (N : ℝ) * (2 * ((2 : ℝ) ^ C / N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (LocalRigidityConsequences.nominal_marginal_bound hNtwo hband) (by norm_num)) hn.le
      _ = _ := by field_simp

end PaperP1.CriticalActualMean
