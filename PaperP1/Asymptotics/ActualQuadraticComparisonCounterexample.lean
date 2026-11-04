module

public import PaperP1.Arithmetic.AdjacentSquarefreeCount
public import PaperP1.Arithmetic.SquarefreeKernelProducts
public import PaperP1.Asymptotics.PrescribedQuadraticKernelTheorem
public import PaperP1.Analysis.ElementaryLogGrowth

/-! # Actual admissible data falsifying the unqualified exact T5.1 comparison

Only the exact displayed comparison is refuted. The asymptotic counting bounds
and their uniform positive-margin formulations remain proved.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualQuadraticComparisonCounterexample

open PaperP1.QuadraticKernelFibres PaperP1.QuadraticKernelExponents

def beta (N : ℕ) : ℝ := Real.log ((N : ℝ) * ((N : ℝ) + 1)) / Real.log N

theorem kernel_value (N : ℕ) (hN : Squarefree N) (hs : Squarefree (N + 1)) :
    kernel 1 N = N * (N + 1) := by
  unfold kernel
  apply PaperP1.SquarefreeKernelProducts.kernel_of_squarefree
  apply (Nat.squarefree_mul (by simp [Nat.coprime_self_add_right])).mpr
  exact ⟨hN, hs⟩

theorem size_identity (N : ℕ) (hN : 2 ≤ N) :
    (N : ℝ) ^ beta N = (N : ℝ) * ((N : ℝ) + 1) := by
  have hp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hne : (N : ℝ) ≠ 1 := ne_of_gt (by exact_mod_cast (show 1 < N by omega))
  exact Real.rpow_logb hp hne (by positivity)

theorem beta_gt_two (N : ℕ) (hN : 2 ≤ N) : 2 < beta N := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hp : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hlt := Real.log_lt_log (sq_pos_of_pos hp)
    (show (N : ℝ) ^ 2 < (N : ℝ) * ((N : ℝ) + 1) by nlinarith)
  rw [Real.log_pow] at hlt
  unfold beta
  apply (lt_div_iff₀ hlog).mpr
  norm_num at hlt
  exact hlt

theorem comparison_failure (N : ℕ) (hN : 2 ≤ N) :
    affine (beta N) 0 < exponent (beta N) 0 := by
  have hb := beta_gt_two N hN
  unfold affine exponent
  rw [max_eq_left (by linarith : 1 - beta N / 2 ≤ beta N / 2 - 0),
    min_eq_right (by linarith : beta N / 2 - 0 ≤ beta N - 0)]
  linarith

theorem source_value (N : ℕ) (hN : 2 ≤ N) (hs : Squarefree N)
    (ht : Squarefree (N + 1)) :
    N ∈ PaperP1.PrescribedQuadraticKernelTheorem.values N 1 1 (beta N) := by
  apply (PaperP1.PrescribedQuadraticKernelTheorem.mem_values N 1 1 N (beta N)).mpr
  rw [size_identity N hN, kernel_value N hs ht]
  have hp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨le_rfl, by omega, ?_, ?_, one_dvd _⟩
  · norm_cast
  · push_cast
    nlinarith

theorem arbitrarily_large_admissible (M : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ N : ℕ, M < N ∧ 2 ≤ N ∧ (1 : ℝ) ≤ (Real.log N) ^ A ∧
      N ∈ PaperP1.PrescribedQuadraticKernelTheorem.values N 1 1 (beta N) ∧
      affine (beta N) (Real.log (1 : ℝ) / Real.log N) <
        exponent (beta N) (Real.log (1 : ℝ) / Real.log N) := by
  obtain ⟨Nlog, hlog⟩ := PaperP1.ElementaryLogGrowth.log_ge_eventually 1
  obtain ⟨N, hN, hs, ht⟩ :=
    PaperP1.AdjacentSquarefreeCount.arbitrarily_large (max M Nlog)
  have hlarge : M < N := by omega
  have htwo : 2 ≤ N := by omega
  refine ⟨N, hlarge, htwo, Real.one_le_rpow (hlog N (by omega)).1 hA,
    source_value N htwo hs ht, ?_⟩
  simpa only [Real.log_one, zero_div] using comparison_failure N htwo

end PaperP1.ActualQuadraticComparisonCounterexample
