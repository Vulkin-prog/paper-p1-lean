module

public import PaperP1.Combinatorics.BoundedIntegerMotifs
public import PaperP1.Asymptotics.SplitOffsetHeightBudget

/-! # Uniform subpolynomial enumeration of all short integer motifs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortMotifBudget

open Finset PaperP1.BoundedSubsetWeights PaperP1.BoundedIntegerMotifs

def motifs (N W : ℕ) (c : ℝ) : Finset (Finset ℤ) :=
  boundedSubsets (offsets W) ⌊c * Real.log (Real.log N)⌋₊

theorem mem_motifs (N W : ℕ) (c : ℝ) (A : Finset ℤ)
    (hcard : (A.card : ℝ) ≤ c * Real.log (Real.log N)) (hA : ∀ a ∈ A, a.natAbs ≤ W) :
    A ∈ motifs N W c := by
  apply (mem_boundedSubsets (offsets W) A _).mpr
  exact ⟨(subset_offsets W A).mpr hA, Nat.le_floor hcard⟩

theorem card_budget (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, 0 < W → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      ((motifs N W c).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let D' := max 1 D
  let K := Real.log 2 + |Real.log (2 * D') + A₀|
  let E := c * K + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨Ne, hNe⟩ := PaperP1.GrowingDegreePrimeError.polylog_error_budget E ε hε
  obtain ⟨Nl, hNl⟩ := Filter.eventually_atTop.mp
    (PaperP1.ModerateOrder.loglog_tendsto_atTop.eventually (Filter.eventually_ge_atTop 1))
  refine ⟨max 2 (max Ne Nl), ?_⟩
  intro N hN W hW hwidth
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hll : 1 ≤ Real.log (Real.log N) := hNl N (by omega)
  have hllpos : 0 < Real.log (Real.log N) := by linarith
  have hD' : 1 ≤ D' := le_max_left _ _
  have hwidth' : (W : ℝ) ≤ D' * (Real.log N) ^ A₀ := hwidth.trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hl.le _))
  have hwlog := PaperP1.SplitOffsetHeightBudget.width_log_bound D' A₀ hD' N W (by omega) hW hll hwidth'
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hWreal : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hbasepos : (0 : ℝ) < 2 * W + 2 := by positivity
  have hbaselog : Real.log (2 * W + 2 : ℝ) ≤ K * Real.log (Real.log N) := by
    have hb : (2 * W + 2 : ℝ) ≤ 2 * (2 * W) := by linarith
    have hlog := Real.log_le_log hbasepos hb
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)] at hlog
    have hconst : Real.log (2 * D') + A₀ ≤ |Real.log (2 * D') + A₀| := le_abs_self _
    have hw := hwlog.trans (mul_le_mul_of_nonneg_right hconst hllpos.le)
    have htwo := mul_le_mul_of_nonneg_left hll hlog2
    dsimp [K]
    nlinarith only [hlog, hw, htwo]
  let m := ⌊c * Real.log (Real.log N)⌋₊
  have hm : (m : ℝ) ≤ c * Real.log (Real.log N) := Nat.floor_le (mul_nonneg hc hllpos.le)
  have hlogbaseNN : 0 ≤ Real.log (2 * W + 2 : ℝ) := Real.log_nonneg (by linarith)
  have hprod : (m : ℝ) * Real.log (2 * W + 2 : ℝ) ≤
      c * K * (Real.log (Real.log N)) ^ 2 := by
    have hmul := mul_le_mul hm hbaselog hlogbaseNN (mul_nonneg hc hllpos.le)
    convert hmul using 1; ring
  have he := hNe N (by omega)
  have heN : E * (Real.log (Real.log N)) ^ 2 ≤ ε * Real.log N := by
    by_contra hnot
    have hstrict := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) hllpos
    nlinarith only [he, hstrict]
  have hone : (1 : ℝ) ≤ (Real.log (Real.log N)) ^ 2 := by nlinarith only [hll]
  have hexp : (m : ℝ) * Real.log (2 * W + 2 : ℝ) + 1 ≤ Real.log N * ε := by
    dsimp [E] at heN
    nlinarith only [hprod, heN, hone]
  calc
    _ ≤ (2 * W + 2 : ℝ) ^ m * Real.exp 1 := bounded_count W m
    _ = Real.exp ((m : ℝ) * Real.log (2 * W + 2 : ℝ) + 1) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hbasepos]
    _ ≤ Real.exp (Real.log N * ε) := Real.exp_le_exp.mpr hexp
    _ = _ := (Real.rpow_def_of_pos hn ε).symm

end PaperP1.ShortMotifBudget
