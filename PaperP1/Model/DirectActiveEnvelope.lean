module

public import PaperP1.Model.MaximumDirectActive
public import PaperP1.Probability.PoissonFactorialMoments

/-! # The actual shifted direct maximum supplies every envelope inequality

The exceptional-event estimate needed to dominate the modified original
count by this envelope is not assumed or claimed proved here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirectActiveEnvelope

open MeasureTheory PaperP1.Model PaperP1.Model.InfiniteRademacher PaperP1.MaximumDirectActive

def envelope (G : Finset ℕ) (L : ℕ) (ω : InfiniteSample) : ℕ := maximum G L ω + 1

theorem observable_integrable (G : Finset ℕ) (L : ℕ) (f : ℕ → ℝ) :
    Integrable (fun ω ↦ f (envelope G L ω)) infiniteRademacherMeasure :=
  MaximumDirectActive.observable_integrable G L (fun n ↦ f (n + 1))

theorem expected_factorial {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ RegularStarts.regularStarts N L) (r : ℕ) :
    (∫ ω, ((envelope G L ω).descFactorial (r + 1) : ℝ) ∂infiniteRademacherMeasure) ≤
      mean G L ^ (r + 1) + (r + 1 : ℕ) * mean G L ^ r := by
  have hi := MaximumDirectActive.observable_integrable G L (fun n ↦ (n.descFactorial (r + 1) : ℝ))
  have hj := (MaximumDirectActive.observable_integrable G L (fun n ↦ (n.descFactorial r : ℝ))).const_mul ((r + 1 : ℕ) : ℝ)
  simp_rw [envelope, PoissonFactorialMoments.descFactorial_succ_add, Nat.cast_add, Nat.cast_mul]
  rw [integral_add hi hj, integral_const_mul]
  simpa only [Nat.cast_add, Nat.cast_one] using
    add_le_add (MaximumDirectActive.expected_factorial hN hL G hG (r + 1))
      (mul_le_mul_of_nonneg_left (MaximumDirectActive.expected_factorial hN hL G hG r) (Nat.cast_nonneg (r + 1)))

theorem expected_power {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ RegularStarts.regularStarts N L) (s : ℝ) (hs : 1 ≤ s) :
    (∫ ω, s ^ envelope G L ω ∂infiniteRademacherMeasure) ≤
      s * (1 + (2 ^ L : ℝ)⁻¹ * (s - 1)) ^ G.card ∧
    (∫ ω, s ^ envelope G L ω ∂infiniteRademacherMeasure) ≤ s * Real.exp ((s - 1) * mean G L) := by
  have hlinear : (∫ ω, s ^ envelope G L ω ∂infiniteRademacherMeasure) =
      (∫ ω, s ^ maximum G L ω ∂infiniteRademacherMeasure) * s := by
    simp_rw [envelope, pow_succ]
    exact integral_mul_const _ _
  rw [hlinear]
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (MaximumDirectActive.expected_power_binomial hN hL G hG s hs) (by linarith : 0 ≤ s)
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (MaximumDirectActive.expected_power_exponential hN hL G hG s hs) (by linarith : 0 ≤ s)

theorem tail_probability {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ RegularStarts.regularStarts N L) (k : ℕ) (hk : 1 ≤ k) :
    infiniteRademacherMeasure.real {ω | k ≤ envelope G L ω} ≤ mean G L ^ (k - 1) / (k - 1).factorial := by
  have hset : {ω | k ≤ envelope G L ω} = {ω | k - 1 ≤ maximum G L ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, envelope]
    omega
  rw [hset]
  exact MaximumDirectActive.tail_probability hN hL G hG (k - 1)

end PaperP1.DirectActiveEnvelope
