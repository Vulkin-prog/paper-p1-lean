module

public import PaperP1.Algebra.FiniteCumulantControl
public import PaperP1.Model.AllFactorialCumulants
public import PaperP1.Asymptotics.FixedQuadraticFactorialMoments
public import PaperP1.Asymptotics.PairActivity

/-! # Every actual fixed factorial cumulant of order at least three has remainder exponent1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedHigherCumulants

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.CountObservables PaperP1.HeterogeneousDirectMaximum

theorem uniform_fixed (r : ℕ) (hr : 3 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        |AllFactorialCumulants.factorialCumulant G L r| ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  let δ := min (ε / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδsmall : δ ≤ 1 / 4 := min_le_right _ _
  let M := max 1 (2 * (2 : ℝ) ^ C)
  have hM : 1 ≤ M := le_max_left _ _
  obtain ⟨B, _hB, hb⟩ := FiniteCumulantControl.finite_bound r hr M hM
  have hper (i : Fin (r + 1)) := FixedQuadraticFactorialMoments.uniform_fixed (max 2 i.val) (le_max_left _ _) C δ hδ
  choose NJ _hNJ hj using hper
  obtain ⟨NA, _hNA, ha⟩ := PairActivity.uniform_cumulant C (δ / 2) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption B (-1 + δ) (ε - δ) (by linarith only [hδε, hε])
  refine ⟨10 + NA + NM + NF + univ.sup NJ, by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let μ := actualMean G L
  let a := RegularCumulantTransfer.secondFactorialCumulant G L
  let τ := (N : ℝ) ^ (-1 + δ)
  have hτ : 0 ≤ τ := Real.rpow_nonneg hn.le _
  have hτone : τ ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδsmall] : -1 + δ ≤ 0)
  have hμ : 0 ≤ μ := sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hμM : μ ≤ M := by
    calc
      _ ≤ actualMean (dyadicBlock N) L := sum_le_sum_of_subset_of_nonneg hG
        (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment Subset.rfl
      _ ≤ 2 * (2 : ℝ) ^ C := (hm N (by omega) L hband).2
      _ ≤ _ := le_max_right _ _
  have hasq : a ^ 2 ≤ τ := by
    have hp := pow_le_pow_left₀ (abs_nonneg a) (ha N (by omega) L hband G hG) 2
    rw [sq_abs] at hp
    have heq : ((N : ℝ) ^ (-2 / 3 + δ / 2)) ^ 2 = (N : ℝ) ^ (-4 / 3 + δ) := by
      rw [pow_two, ← Real.rpow_add hn]
      congr 1
      ring
    rw [heq] at hp
    exact hp.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only []))
  have herror (j : ℕ) (hjcap : j ≤ r) :
      |factorialCountMoment G L j - μ ^ j - (j.choose 2 : ℝ) * μ ^ (j - 2) * a| ≤ τ := by
    by_cases hjtwo : 2 ≤ j
    · let i : Fin (r + 1) := ⟨j, by omega⟩
      have hNi : NJ i ≤ univ.sup NJ := le_sup (f := NJ) (mem_univ i)
      have h := hj i N (by omega) L hband G hG
      simpa only [i, max_eq_right hjtwo] using h
    · have hsmall : j = 0 ∨ j = 1 := by omega
      rcases hsmall with rfl | rfl
      · have hzero : factorialCountMoment G L 0 = 1 := by
          rw [factorialCountMoment_eq_subset hG 0]
          simp only [Nat.factorial_zero, Nat.cast_one, powersetCard_zero, sum_singleton, infiniteJointMoment_empty, mul_one]
        simpa only [hzero, pow_zero, Nat.choose_eq_zero_of_lt (by decide : 0 < 2), Nat.cast_zero,
          zero_mul, sub_self, sub_zero, abs_zero] using hτ
      · have hone : factorialCountMoment G L 1 = μ := by
          rw [factorialCountMoment_one, countMoment_one hG]
          rfl
        simpa only [hone, pow_one, Nat.choose_eq_zero_of_lt (by decide : 1 < 2), Nat.cast_zero,
          zero_mul, sub_self, sub_zero, abs_zero] using hτ
  have hdata : QuadraticCumulantBound.Data (AllFactorialCumulants.series G L) μ a M τ r := by
    refine ⟨AllFactorialCumulants.series_constant hG, ?_, ?_, hμ, hμM, hτ, hτone, hasq, ?_⟩
    · rw [AllFactorialCumulants.moment_series, factorialCountMoment_one, countMoment_one hG]
      rfl
    · exact AllFactorialCumulants.cumulant_two hG
    · intro j hjcap
      rw [AllFactorialCumulants.moment_series]
      simpa only [QuadraticMomentRecurrence.quadratic, sub_sub] using herror j hjcap
  have hbound := hb (AllFactorialCumulants.series G L) μ a τ hdata
  calc
    _ ≤ B * τ := hbound
    _ ≤ (N : ℝ) ^ ((-1 + δ) + (ε - δ)) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.FixedHigherCumulants
