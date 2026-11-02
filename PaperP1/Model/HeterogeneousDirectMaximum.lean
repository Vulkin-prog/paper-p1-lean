module

public import PaperP1.Model.DirectActiveEnvelope
public import PaperP1.Probability.HeterogeneousActiveMaximum
public import Mathlib.Tactic.Push

/-! # Direct-maximum bounds with the exact mean on every finite actual ground set

Regularity and positive local marginals are unnecessary. Null marginals are
handled explicitly, and every source joint factor is proved in the model.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeterogeneousDirectMaximum

open Finset MeasureTheory PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.HereditaryActiveMaximum PaperP1.MaximumDirectActive PaperP1.DirectActiveEnvelope

def actualMean (G : Finset ℕ) (L : ℕ) : ℝ := ∑ x ∈ G, infiniteMarginal x L

theorem direct_joint_factor (L : ℕ) (hL : 0 < L) (A : Finset ℕ)
    (hzero : runRelativeNullity L A = 0) :
    infiniteJointMoment L A = ∏ x ∈ A, infiniteMarginal x L := by
  by_cases hp : ∀ x ∈ A, 0 < infiniteMarginal x L
  · exact CompressedJointMoments.direct_joint_factor L hL A hp hzero
  · push Not at hp
    obtain ⟨x, hx, hp⟩ := hp
    have hz : infiniteMarginal x L = 0 := le_antisymm hp (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    have hq : infiniteJointMoment L A ≤ infiniteMarginal x L := by
      simpa only [InfiniteTripleCancellation.singleton_joint] using
        MissingBlockProbabilities.infiniteJointMoment_antitone L (singleton_subset_iff.mpr hx)
    have hqzero : infiniteJointMoment L A = 0 := le_antisymm (by linarith only [hq, hz])
      (infiniteJointMoment_nonneg L A)
    rw [hqzero, prod_eq_zero hx hz]

theorem finite_joint_product (G : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (A : Finset ℕ) (hA : A ∈ families G L) :
    finiteJointMoment (cylinderProbability (cutoff G L)) (fun x ↦ startIndicator x L) A =
      ∏ x ∈ A, infiniteMarginal x L := by
  obtain ⟨hAG, hzero⟩ := mem_families.mp hA
  have hcut (x : ℕ) (hx : x ∈ A) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) (hAG hx)
  rw [← infiniteJointMoment_eq_finite (cutoff G L) L A hcut]
  exact direct_joint_factor L hL A hzero

theorem actualMean_eq_countMoment {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    actualMean G L = CountObservables.countMoment G L 1 := (CountObservables.countMoment_one hG).symm

theorem expected_choose_elementary (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (r : ℕ) :
    (∫ ω, ((maximum G L ω).choose r : ℝ) ∂infiniteRademacherMeasure) ≤
      SubsetPowerSums.elementary (fun x ↦ infiniteMarginal x L) G r := by
  rw [observable_integral G L (fun n ↦ (n.choose r : ℝ))]
  exact HeterogeneousActiveMaximum.expected_choose_elementary _ G (families G L) (empty_mem G L)
    (families_hereditary G L) (fun _ hA ↦ (mem_families.mp hA).1) _ _
    (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    (fun A hA ↦ (finite_joint_product G L hL A hA).le) r

theorem expected_choose_poisson (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (r : ℕ) :
    (∫ ω, ((maximum G L ω).choose r : ℝ) ∂infiniteRademacherMeasure) ≤ actualMean G L ^ r / r.factorial := by
  rw [observable_integral G L (fun n ↦ (n.choose r : ℝ))]
  exact HeterogeneousActiveMaximum.expected_choose_poisson _ G (families G L) (empty_mem G L)
    (families_hereditary G L) (fun _ hA ↦ (mem_families.mp hA).1) _ _
    (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    (fun A hA ↦ (finite_joint_product G L hL A hA).le) r

theorem expected_factorial (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (r : ℕ) :
    (∫ ω, ((maximum G L ω).descFactorial r : ℝ) ∂infiniteRademacherMeasure) ≤ actualMean G L ^ r := by
  rw [observable_integral G L (fun n ↦ (n.descFactorial r : ℝ))]
  exact HeterogeneousActiveMaximum.expected_factorial _ G (families G L) (empty_mem G L)
    (families_hereditary G L) (fun _ hA ↦ (mem_families.mp hA).1) _ _
    (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    (fun A hA ↦ (finite_joint_product G L hL A hA).le) r

theorem expected_power_product (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (s : ℝ) (hs : 1 ≤ s) :
    (∫ ω, s ^ maximum G L ω ∂infiniteRademacherMeasure) ≤
      ∏ x ∈ G, (1 + (s - 1) * infiniteMarginal x L) := by
  rw [observable_integral]
  exact HeterogeneousActiveMaximum.expected_power_product _ G (families G L) (empty_mem G L)
    (families_hereditary G L) (fun _ hA ↦ (mem_families.mp hA).1) _ _
    (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    (fun A hA ↦ (finite_joint_product G L hL A hA).le) s hs

theorem expected_power_exponential (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (s : ℝ) (hs : 1 ≤ s) :
    (∫ ω, s ^ maximum G L ω ∂infiniteRademacherMeasure) ≤ Real.exp ((s - 1) * actualMean G L) := by
  rw [observable_integral]
  exact HeterogeneousActiveMaximum.expected_power_exponential _ G (families G L) (empty_mem G L)
    (families_hereditary G L) (fun _ hA ↦ (mem_families.mp hA).1) _ _
    (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    (fun A hA ↦ (finite_joint_product G L hL A hA).le) s hs

theorem tail_probability (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (r : ℕ) :
    infiniteRademacherMeasure.real {ω | r ≤ maximum G L ω} ≤ actualMean G L ^ r / r.factorial := by
  rw [tail_probability_eq_finite]
  exact HeterogeneousActiveMaximum.tail_bound _ G (families G L) (empty_mem G L)
    (families_hereditary G L) (fun _ hA ↦ (mem_families.mp hA).1) _ _
    (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    (fun A hA ↦ (finite_joint_product G L hL A hA).le) r

theorem envelope_factorial (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (r : ℕ) :
    (∫ ω, ((envelope G L ω).descFactorial (r + 1) : ℝ) ∂infiniteRademacherMeasure) ≤
      actualMean G L ^ (r + 1) + (r + 1 : ℕ) * actualMean G L ^ r := by
  have hi := MaximumDirectActive.observable_integrable G L (fun n ↦ (n.descFactorial (r + 1) : ℝ))
  have hj := (MaximumDirectActive.observable_integrable G L (fun n ↦ (n.descFactorial r : ℝ))).const_mul ((r + 1 : ℕ) : ℝ)
  simp_rw [envelope, PoissonFactorialMoments.descFactorial_succ_add, Nat.cast_add, Nat.cast_mul]
  rw [integral_add hi hj, integral_const_mul]
  simpa only [Nat.cast_add, Nat.cast_one] using
    add_le_add (expected_factorial G L hL (r + 1))
      (mul_le_mul_of_nonneg_left (expected_factorial G L hL r) (Nat.cast_nonneg (r + 1)))

theorem envelope_power (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (s : ℝ) (hs : 1 ≤ s) :
    (∫ ω, s ^ envelope G L ω ∂infiniteRademacherMeasure) ≤
      s * ∏ x ∈ G, (1 + (s - 1) * infiniteMarginal x L) ∧
    (∫ ω, s ^ envelope G L ω ∂infiniteRademacherMeasure) ≤ s * Real.exp ((s - 1) * actualMean G L) := by
  have hlinear : (∫ ω, s ^ envelope G L ω ∂infiniteRademacherMeasure) =
      (∫ ω, s ^ maximum G L ω ∂infiniteRademacherMeasure) * s := by
    simp_rw [envelope, pow_succ]
    exact integral_mul_const _ _
  rw [hlinear]
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_right (expected_power_product G L hL s hs) (by linarith : 0 ≤ s)
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_right (expected_power_exponential G L hL s hs) (by linarith : 0 ≤ s)

theorem envelope_tail (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (k : ℕ) (hk : 1 ≤ k) :
    infiniteRademacherMeasure.real {ω | k ≤ envelope G L ω} ≤ actualMean G L ^ (k - 1) / (k - 1).factorial := by
  have hset : {ω | k ≤ envelope G L ω} = {ω | k - 1 ≤ maximum G L ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, envelope]
    omega
  rw [hset]
  exact tail_probability G L hL (k - 1)

end PaperP1.HeterogeneousDirectMaximum
