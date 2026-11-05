module

public import PaperP1.Model.AllPairResidualMass
public import PaperP1.Asymptotics.RetainedBadPairActivity
public import PaperP1.Asymptotics.PositionalRestorationRates
public import PaperP1.Asymptotics.ContactSeedKernel

/-! # The actual positive residual mass tau in companion T19.14 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairResidualMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.AllPairResidualMass

theorem uniform_local (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → localMass N L ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NP, hp⟩ := TripleRankGeometry.critical_nominal_marginal_cap C
  obtain ⟨NI, _hNI, hi⟩ := PositionalRestorationRates.nominal_discarded_mass C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NP + NI + NF, by omega, ?_⟩
  intro N hN L hband
  have hcap : localMass N L ≤ 2 * ∑ _x ∈ RegularStarts.irregularStarts N L, (2 ^ L : ℝ)⁻¹ := by
    rw [mul_sum]
    apply sum_le_sum
    intro x hx
    exact hp N (by omega) L hband x (mem_sdiff.mp hx).1
  apply hcap.trans
  have hh := mul_le_mul_of_nonneg_left (hi N (by omega) L hband) (by norm_num : (0 : ℝ) ≤ 2)
  apply hh.trans
  convert hf N (by omega) using 1
  congr 1
  ring

theorem uniform_tau (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        tau (8 * (L + 1) : ℕ) N L ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NB, _hNB, hb⟩ := RetainedBadPairActivity.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NL, _hNL, hl⟩ := uniform_local C (ε / 2) (by positivity)
  obtain ⟨NC, _hNC, hc⟩ := ContactSeedKernel.uniform_joint_mass C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NB + NL + NC + NG + NF, by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  have hfinite := AllPairResidualMass.finite_bound (8 * (L + 1) : ℕ) N L hL
  have hbad := hb N (by omega) L hband
  have hlocal := hl N (by omega) L hband
  have hcontact := hc N (by omega) L hband (RegularStarts.regularStarts N L)
    (RegularStarts.regularStarts_subset N L)
  have hpower : (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [])
  have hfactor : 3 * (N : ℝ) ^ (-4 / 5 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hnonneg : 0 ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  linarith only [hfinite, hbad, hlocal.trans hpower, hcontact.trans hpower, hfactor, hnonneg]

end PaperP1.AllPairResidualMass
