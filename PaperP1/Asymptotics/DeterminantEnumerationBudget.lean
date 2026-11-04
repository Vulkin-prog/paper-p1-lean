module

public import PaperP1.Arithmetic.DeterminantPrimitiveReduction
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount
public import PaperP1.Arithmetic.LogarithmicPrimeCount
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # All actual smooth-part, dyadic-box and primitive-reduction choices are subpolynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantEnumerationBudget

open Filter Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantPrimitiveReduction

theorem index_bound (X : ℕ) : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ Real.log X / Real.log 2 + 1 := by
  have hh := Real.natLog_le_logb X 2
  norm_num only [Nat.cast_ofNat] at hh
  unfold Real.logb at hh
  push_cast
  linarith only [hh]

theorem box_logarithmic_bound (Q : ℕ) (hQ : 1 ≤ Q) {N : ℕ} (hN : 2 ≤ N)
    (hH : 1 ≤ Real.log N) :
    ((boxes (Q * N)).card : ℝ) ≤
      ((1 + Real.log Q) / Real.log 2 + 1) ^ 4 * (Real.log N) ^ 4 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hi := index_bound (Q * N)
  have hlog : Real.log ((Q * N : ℕ) : ℝ) = Real.log Q + Real.log N := by
    rw [Nat.cast_mul, Real.log_mul hq.ne' hn.ne']
  rw [hlog] at hi
  have hfactor : 0 ≤ Real.log Q / Real.log 2 + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_right hH hfactor
  have hm' : Real.log Q / Real.log 2 + 1 ≤ (Real.log Q / Real.log 2 + 1) * Real.log N := by
    simpa only [one_mul, mul_comm] using hm
  rw [add_div] at hi
  have hi' : ((Nat.log 2 (Q * N) + 1 : ℕ) : ℝ) ≤
      ((1 + Real.log Q) / Real.log 2 + 1) * Real.log N := by
    have hnorm : ((1 + Real.log Q) / Real.log 2 + 1) * Real.log N =
        Real.log N / Real.log 2 + (Real.log Q / Real.log 2 + 1) * Real.log N := by ring
    rw [hnorm]
    linarith only [hi, hm']
  rw [boxes_card, Nat.cast_pow]
  simpa only [mul_pow] using pow_le_pow_left₀ (Nat.cast_nonneg _) hi' 4

theorem boxes_subpolynomial (Q : ℕ) (hQ : 1 ≤ Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ((boxes (Q * N)).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NP, hP⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (((1 + Real.log Q) / Real.log 2 + 1) ^ 4) 4 ε hε
  have ht : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NH, hH⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max NP NH, ?_⟩
  intro N hN
  have hb := box_logarithmic_bound Q hQ (by omega : 2 ≤ N) (hH N (by omega))
  have hp := hP N (by omega)
  rw [← Real.rpow_natCast (Real.log N) 4] at hb
  exact hb.trans hp

theorem reductions_subpolynomial (D A ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ h : ℕ, (h : ℝ) ≤ D * (Real.log N) ^ A →
      ((reductions h).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hP⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow (D ^ 2) (2 * A) ε hε
  refine ⟨N₀, ?_⟩
  intro N hN h hshift
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hH : 0 < Real.log N := Real.log_pos hn
  have hh : ((reductions h).card : ℝ) ≤ (h : ℝ) ^ 2 := by exact_mod_cast reductions_card h
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg h) hshift 2
  have heq : (D * (Real.log N) ^ A) ^ 2 = D ^ 2 * (Real.log N) ^ (2 * A) := by
    rw [mul_pow, ← Real.rpow_natCast ((Real.log N) ^ A) 2, ← Real.rpow_mul hH.le]
    congr 2
    ring
  rw [heq] at hs
  exact (hh.trans hs).trans (hP N (by omega))

theorem total_subpolynomial (Q : ℕ) (hQ : 1 ≤ Q) (D E A ε : ℝ)
    (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ H h : ℕ,
      (H : ℝ) ≤ D * Real.log N → (h : ℝ) ≤ E * (Real.log N) ^ A →
      (((PaperP1.DefectCounting.smallPrimesUpTo H).powerset.card : ℝ) ^ 2 *
        (boxes (Q * N)).card * (reductions h).card) ≤ (N : ℝ) ^ ε := by
  let η := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NS, hS⟩ := PaperP1.LogarithmicPrimeCount.smooth_support_count_le_rpow_eventually D hD η hη
  obtain ⟨NB, hB⟩ := boxes_subpolynomial Q hQ η hη
  obtain ⟨NR, hR⟩ := reductions_subpolynomial E A η hη
  refine ⟨max NS (max NB NR), ?_⟩
  intro N hN H h hH hh
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg _) (hS N (by omega) H hH) 2
  have hb := hB N (by omega)
  have hr := hR N (by omega) h hh
  calc
    _ ≤ ((N : ℝ) ^ η) ^ 2 * (N : ℝ) ^ η * (N : ℝ) ^ η :=
      mul_le_mul (mul_le_mul hs hb (Nat.cast_nonneg _) (by positivity)) hr
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by
      rw [pow_two, ← Real.rpow_add hn, ← Real.rpow_add hn, ← Real.rpow_add hn]
      congr 1
      dsimp [η]
      ring

end PaperP1.DeterminantEnumerationBudget
