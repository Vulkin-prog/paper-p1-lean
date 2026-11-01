module

public import PaperP1.Probability.PushforwardMass
public import PaperP1.Probability.RawRecurrence
public import PaperP1.Probability.PoissonFactorialMoments

/-! # Independent Poisson mass products and bounded summation identities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonProduct

open PaperP1.PoissonSequence PaperP1.PoissonPartialSums PaperP1.AtomicTests

def joint (a b : ℝ) (z : ℕ × ℕ) : ℝ := mass a z.1 * mass b z.2

theorem joint_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℕ × ℕ) : 0 ≤ joint a b z :=
  mul_nonneg (mass_nonneg ha z.1) (mass_nonneg hb z.2)

theorem joint_summable {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Summable (joint a b) :=
  (hasSum_mass a ha).summable.mul_of_nonneg (hasSum_mass b hb).summable
    (mass_nonneg ha) (mass_nonneg hb)

theorem joint_hasSum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : HasSum (joint a b) 1 := by
  apply (joint_summable ha hb).hasSum_iff.mpr
  rw [(joint_summable ha hb).tsum_prod]
  simp only [joint, tsum_mul_left, (hasSum_mass b hb).tsum_eq, mul_one, (hasSum_mass a ha).tsum_eq]

theorem poisson_moment_hasSum {a : ℝ} (ha : 0 ≤ a) :
    HasSum (fun k : ℕ ↦ (k : ℝ) * mass a k) a := by
  simpa only [Nat.descFactorial_one, pow_one, mul_comm] using
    PoissonFactorialMoments.hasSum_mass_factorial a ha 1

theorem left_moment_summable {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Summable (fun z : ℕ × ℕ ↦ (z.1 : ℝ) * joint a b z) := by
  have hs := (poisson_moment_hasSum ha).summable.mul_of_nonneg (hasSum_mass b hb).summable
    (fun k ↦ mul_nonneg (Nat.cast_nonneg k) (mass_nonneg ha k)) (mass_nonneg hb)
  simpa only [joint, mul_assoc] using hs

theorem right_moment_summable {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Summable (fun z : ℕ × ℕ ↦ (z.2 : ℝ) * joint a b z) := by
  have hs := (hasSum_mass a ha).summable.mul_of_nonneg (poisson_moment_hasSum hb).summable
    (mass_nonneg ha) (fun k ↦ mul_nonneg (Nat.cast_nonneg k) (mass_nonneg hb k))
  convert hs using 1
  funext z
  unfold joint
  ring

theorem poisson_test_identity {a : ℝ} (ha : 0 ≤ a) (f : ℕ → ℝ) (hf : ∀ k, |f k| ≤ 1) :
    (∑' k : ℕ, (k : ℝ) * mass a k * f k) = a * ∑' k, mass a k * f (k + 1) := by
  have heq : ∀ k : ℕ, (k : ℝ) * mass a k = a * shift (mass a) k := by
    intro k
    cases k with
    | zero => simp
    | succ k => simpa only [shift_succ, Nat.cast_add, Nat.cast_one, mul_comm] using mass_succ_mul a k
  calc
    _ = ∑' k, a * (shift (mass a) k * f k) := tsum_congr (fun k ↦ by rw [heq]; ring)
    _ = a * ∑' k, shift (mass a) k * f k := tsum_mul_left
    _ = _ := by rw [RawRecurrence.shifted_test_sum (hasSum_mass a ha).summable f hf]

theorem tsum_left {g : ℕ × ℕ → ℝ} (hg : Summable g) :
    (∑' z, g z) = ∑' m : ℕ, ∑' n : ℕ, g (n, m) := by
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq g]
  exact hg.prod_symm.tsum_prod

theorem left_test_identity {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (F : ℕ × ℕ → ℝ) (hF : ∀ z, |F z| ≤ 1) :
    (∑' z : ℕ × ℕ, (z.1 : ℝ) * joint a b z * F z) =
      a * ∑' z : ℕ × ℕ, joint a b z * F (z.1 + 1, z.2) := by
  have hleft := summable_mul_unit (left_moment_summable ha hb) hF
  have hright := summable_mul_unit (joint_summable ha hb) (fun z ↦ hF (z.1 + 1, z.2))
  rw [tsum_left hleft, tsum_left hright, ← tsum_mul_left]
  apply tsum_congr
  intro m
  have hid := poisson_test_identity ha (fun n ↦ F (n, m)) (fun n ↦ hF (n, m))
  calc
    _ = mass b m * ∑' n : ℕ, (n : ℝ) * mass a n * F (n, m) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      unfold joint
      ring
    _ = mass b m * (a * ∑' n, mass a n * F (n + 1, m)) := by rw [hid]
    _ = _ := by
      rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
      apply tsum_congr
      intro n
      unfold joint
      ring

theorem right_test_identity {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (F : ℕ × ℕ → ℝ) (hF : ∀ z, |F z| ≤ 1) :
    (∑' z : ℕ × ℕ, (z.2 : ℝ) * joint a b z * F z) =
      b * ∑' z : ℕ × ℕ, joint a b z * F (z.1, z.2 + 1) := by
  have hleft := summable_mul_unit (right_moment_summable ha hb) hF
  have hright := summable_mul_unit (joint_summable ha hb) (fun z ↦ hF (z.1, z.2 + 1))
  rw [hleft.tsum_prod, hright.tsum_prod, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have hid := poisson_test_identity hb (fun m ↦ F (n, m)) (fun m ↦ hF (n, m))
  calc
    _ = mass a n * ∑' m : ℕ, (m : ℝ) * mass b m * F (n, m) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      unfold joint
      ring
    _ = mass a n * (b * ∑' m, mass b m * F (n, m + 1)) := by rw [hid]
    _ = _ := by
      rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
      apply tsum_congr
      intro m
      unfold joint
      ring

end PaperP1.PoissonProduct
