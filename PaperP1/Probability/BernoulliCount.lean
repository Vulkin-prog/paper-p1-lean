module

public import PaperP1.Probability.FiniteCoupling

/-! # Any indicator count bounded by one has its Bernoulli law with the exact mean -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Probability

open Finset PaperP1.Algebra

theorem atom_eq_bernoulli_of_le_one {n : ℕ} (hn : n ≤ 1) :
    (atom n : SignedLaw ℝ) = bernoulli (n : ℝ) := by
  have heq : n = 0 ∨ n = 1 := by omega
  rcases heq with rfl | rfl
  · simp [bernoulli]
  · rw [bernoulli, Nat.cast_one, map_one, one_mul, forwardDifference, atom_zero]
    ring

theorem countLaw_eq_bernoulli {Ω ι : Type*} [Fintype Ω]
    (P : FiniteProbability Ω) (G : Finset ι) (J : ι → Ω → Bool)
    (hcount : ∀ ω, indicatorCount G J ω ≤ 1) :
    countLaw G P.weight J = bernoulli (∑ x ∈ G, exactMarginal P J x) := by
  classical
  have hpoint (ω : Ω) : (atom (indicatorCount G J ω) : SignedLaw ℝ) =
      bernoulli (indicatorCount G J ω : ℝ) := atom_eq_bernoulli_of_le_one (hcount ω)
  have hmean := mean_indicatorCount P G J
  unfold countLaw
  simp_rw [hpoint, bernoulli, atom_zero, mul_add, mul_one, ← mul_assoc, ← map_mul scalar]
  rw [sum_add_distrib, ← map_sum, P.total_weight, map_one, ← sum_mul, ← map_sum]
  change 1 + scalar (finiteExpectation P.weight (fun ω ↦ (indicatorCount G J ω : ℝ))) * forwardDifference = _
  rw [hmean]

end PaperP1.Probability
