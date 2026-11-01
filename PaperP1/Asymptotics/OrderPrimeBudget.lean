module

public import PaperP1.Asymptotics.OrderDependentBranching
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # The actual rounded prime budget, uniformly in the exposure order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrderPrimeBudget

open Finset Filter PaperP1.Model PaperP1.DefectCounting PaperP1.LocalDefectBound
  PaperP1.OldPrimeCardinality PaperP1.CriticalBandScale

def coefficient : ℝ := 5 * upperScale + 1

theorem coefficient_pos : 0 < coefficient := by
  unfold coefficient
  have h := upperScale_pos
  positivity

theorem primeCount_le (B : ℕ) : primeCount B ≤ B := by
  have hsub : smallPrimesUpTo B ⊆ Icc 1 B := by
    intro p hp
    obtain ⟨hp, hpB⟩ := mem_smallPrimesUpTo.mp hp
    exact mem_Icc.mpr ⟨hp.pos, hpB⟩
  simpa only [primeCount, Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub

theorem width_le_budget {N L j : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N)
    (hj : 1 ≤ j) (hlogB : 0 < Real.log (L + 1 : ℕ)) :
    L + 1 ≤ primeCountBudget N L j := by
  push_cast at hlogB
  have hBpos : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have hBupper : (L : ℝ) + 1 ≤ (3 * N : ℕ) := by exact_mod_cast (show L + 1 ≤ 3 * N by omega)
  have hlog3 := Real.log_le_log hBpos hBupper
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hlarge : (L : ℝ) + 1 ≤
      (j : ℝ) * (L + 1) * Real.log (3 * N : ℕ) / Real.log (L + 1) := by
    apply (le_div_iff₀ hlogB).mpr
    have h1 := mul_le_mul_of_nonneg_left hlog3 hBpos.le
    have h2 := mul_le_mul_of_nonneg_right hjR
      (mul_nonneg hBpos.le (hlogB.le.trans hlog3))
    push_cast at hlogB h1
    nlinarith
  have hceil := Nat.le_ceil
    ((primeCount (L + 1) : ℝ) + (j : ℝ) * (L + 1) *
      Real.log (3 * N : ℕ) / Real.log (L + 1))
  have hpc : (0 : ℝ) ≤ primeCount (L + 1) := Nat.cast_nonneg _
  have hbudget : (L : ℝ) + 1 ≤ (primeCountBudget N L j : ℝ) := by
    dsimp only [primeCountBudget]
    linarith
  exact_mod_cast hbudget

theorem finite_upper {N L j : ℕ} (hN : 3 ≤ N) (hj : 1 ≤ j)
    (hh : 1 ≤ Real.log (Real.log N))
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N)
    (hlogB : Real.log (Real.log N) / 2 ≤ Real.log (L + 1 : ℕ)) :
    (primeCountBudget N L j : ℝ) ≤
      coefficient * j * (Real.log N) ^ 2 / Real.log (Real.log N) := by
  push_cast at hwidth hlogB
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hH : 0 < Real.log N := Real.log_pos (by linarith)
  have hh0 : 0 < Real.log (Real.log N) := by linarith
  have hlogB0 : 0 < Real.log ((L : ℝ) + 1) := by linarith
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hu := upperScale_pos
  have hhH := Real.log_le_self hH.le
  have hH1 : 1 ≤ Real.log N := by linarith
  have hratio : Real.log N ≤ (Real.log N) ^ 2 / Real.log (Real.log N) := by
    apply (le_div_iff₀ hh0).mpr
    nlinarith
  have hratio0 : 0 ≤ (Real.log N) ^ 2 / Real.log (Real.log N) := by positivity
  have hratio1 : 1 ≤ (Real.log N) ^ 2 / Real.log (Real.log N) := hH1.trans hratio
  have hthree : Real.log (3 * N : ℕ) ≤ 2 * Real.log N := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 3 * N)
      (by nlinarith : 3 * (N : ℝ) ≤ (N : ℝ) ^ 2)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.log_pow] using h
  have hterm : (j : ℝ) * (L + 1) * Real.log (3 * N : ℕ) / Real.log (L + 1) ≤
      4 * upperScale * j * (Real.log N) ^ 2 / Real.log (Real.log N) := by
    calc
      _ ≤ ((j : ℝ) * (upperScale * Real.log N) * (2 * Real.log N)) /
          Real.log ((L : ℝ) + 1) := by
        apply div_le_div_of_nonneg_right _ hlogB0.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add, Nat.cast_one] using hwidth)
          (Nat.cast_nonneg j)) hthree (Real.log_natCast_nonneg _) (by positivity)
      _ ≤ ((j : ℝ) * (upperScale * Real.log N) * (2 * Real.log N)) /
          (Real.log (Real.log N) / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hlogB
      _ = _ := by ring
  have hpcR : (primeCount (L + 1) : ℝ) ≤ (L : ℝ) + 1 := by exact_mod_cast primeCount_le (L + 1)
  have hpc : (primeCount (L + 1) : ℝ) ≤ upperScale * Real.log N := hpcR.trans hwidth
  have hpc' : (primeCount (L + 1) : ℝ) ≤
      upperScale * j * ((Real.log N) ^ 2 / Real.log (Real.log N)) := by
    have hmul := mul_le_mul_of_nonneg_right hjR hratio0
    simp only [one_mul] at hmul
    have hmul' := mul_le_mul_of_nonneg_left (hratio.trans hmul) hu.le
    exact hpc.trans (by simpa only [one_mul, mul_assoc] using hmul')
  have hone : (1 : ℝ) ≤ (j : ℝ) * ((Real.log N) ^ 2 / Real.log (Real.log N)) := by
    nlinarith
  have hlog30 := Real.log_natCast_nonneg (3 * N)
  have hceil := (Nat.ceil_lt_add_one
    (show 0 ≤ (primeCount (L + 1) : ℝ) + (j : ℝ) * (L + 1) *
      Real.log (3 * N : ℕ) / Real.log (L + 1) by positivity)).le
  change (primeCountBudget N L j : ℝ) ≤ _ at hceil
  unfold coefficient
  ring_nf at hterm hpc' hone hceil ⊢
  nlinarith

theorem finite_root_bound {N L j : ℕ} (hN : 3 ≤ N) (hLN : L ≤ N) (hj : 1 ≤ j)
    (hh : 1 ≤ Real.log (Real.log N))
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N)
    (hlogB : Real.log (Real.log N) / 2 ≤ Real.log (L + 1 : ℕ)) :
    Real.sqrt ((primeCountBudget N L j : ℝ) /
      Real.log ((primeCountBudget N L j : ℝ) + 2)) ≤
        Real.sqrt (2 * coefficient) * Real.sqrt j *
          (Real.log N / Real.log (Real.log N)) := by
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hH : 0 < Real.log N := Real.log_pos (by linarith)
  have hh0 : 0 < Real.log (Real.log N) := by linarith
  have hlogB0 : 0 < Real.log (L + 1 : ℕ) := by linarith
  have hm := width_le_budget (by omega : 2 ≤ N) hLN hj hlogB0
  have hmR : ((L + 1 : ℕ) : ℝ) ≤ primeCountBudget N L j := by exact_mod_cast hm
  have hlogm : Real.log (Real.log N) / 2 ≤
      Real.log ((primeCountBudget N L j : ℝ) + 2) := by
    exact hlogB.trans (Real.log_le_log (by positivity)
      (by linarith : ((L + 1 : ℕ) : ℝ) ≤ (primeCountBudget N L j : ℝ) + 2))
  have hupper := finite_upper hN hj hh hwidth hlogB
  have hratio : (primeCountBudget N L j : ℝ) /
      Real.log ((primeCountBudget N L j : ℝ) + 2) ≤
        2 * coefficient * j * (Real.log N) ^ 2 / (Real.log (Real.log N)) ^ 2 := by
    calc
      _ ≤ (coefficient * j * (Real.log N) ^ 2 / Real.log (Real.log N)) /
          Real.log ((primeCountBudget N L j : ℝ) + 2) :=
        div_le_div_of_nonneg_right hupper (by linarith)
      _ ≤ (coefficient * j * (Real.log N) ^ 2 / Real.log (Real.log N)) /
          (Real.log (Real.log N) / 2) :=
        div_le_div_of_nonneg_left (by have h := coefficient_pos; positivity) (by linarith) hlogm
      _ = _ := by ring
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hcoef := Real.sq_sqrt (show 0 ≤ 2 * coefficient by have h := coefficient_pos; positivity)
  have hjroot := Real.sq_sqrt (show (0 : ℝ) ≤ j by exact Nat.cast_nonneg j)
  calc
    _ ≤ 2 * coefficient * j * (Real.log N) ^ 2 / (Real.log (Real.log N)) ^ 2 := hratio
    _ = _ := by rw [mul_pow, mul_pow, div_pow, hcoef, hjroot]; ring

theorem critical_conditions (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        L ≤ N ∧ 1 ≤ Real.log (Real.log N) ∧
          ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N ∧
          Real.log (Real.log N) / 2 ≤ Real.log (L + 1 : ℕ) := by
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Nh, hNh⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp PrimeLogBudget.log_nat_tendsto_atTop).eventually
      (eventually_ge_atTop (max 1 (2 * |Real.log lowerScale|))))
  refine ⟨max 3 (max Ngeom Nh), by omega, ?_⟩
  intro N hN L hband
  obtain ⟨hN2, _, hB2, hthin, hlo, hhi⟩ := hgeom N (by omega) L hband
  have hh : max 1 (2 * |Real.log lowerScale|) ≤ Real.log (Real.log N) := hNh N (by omega)
  have hH : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog := Real.log_le_log (mul_pos lowerScale_pos hH) hlo
  rw [Real.log_mul lowerScale_pos.ne' hH.ne'] at hlog
  refine ⟨by omega, (le_max_left _ _).trans hh, hhi, ?_⟩
  have habs := neg_abs_le (Real.log lowerScale)
  have hlarge := (le_max_right _ _).trans hh
  linarith

theorem critical_root_bound (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ j : ℕ, 1 ≤ j →
        Real.sqrt ((primeCountBudget N L j : ℝ) /
          Real.log ((primeCountBudget N L j : ℝ) + 2)) ≤
            Real.sqrt (2 * coefficient) * Real.sqrt j *
              (Real.log N / Real.log (Real.log N)) := by
  obtain ⟨N₀, hN₀, hconditions⟩ := critical_conditions C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband j hj
  obtain ⟨hLN, hh, hwidth, hlogB⟩ := hconditions N hN L hband
  exact finite_root_bound (by omega) hLN hj hh hwidth hlogB

end PaperP1.OrderPrimeBudget
