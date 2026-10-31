module

public import PaperP1.Probability.Convolution
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Ordinary ℓ¹ norm for finite signed count laws

This is the unweighted norm `Σ_k |ν{k}|` used in the paper. In particular it
does not charge the size of the suffix count. Coefficient nonnegativity gives
norm equal to mass, and convolution is submultiplicative.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace PaperP1.Probability

/-- The ordinary, unweighted ℓ¹ norm of a finitely supported signed law. -/
def l1Norm (ν : SignedLaw ℝ) : ℝ := ν.coeff.sum fun _ r => |r|

theorem l1Norm_nonneg (ν : SignedLaw ℝ) : 0 ≤ l1Norm ν := by
  unfold l1Norm Finsupp.sum
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

@[simp]
theorem l1Norm_zero : l1Norm 0 = 0 := by simp [l1Norm]

theorem l1Norm_single (n : ℕ) (r : ℝ) :
    l1Norm (AddMonoidAlgebra.single n r) = |r| := by
  unfold l1Norm
  rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index]
  simp

@[simp]
theorem l1Norm_atom (n : ℕ) : l1Norm (atom n : SignedLaw ℝ) = 1 := by
  simpa [atom] using l1Norm_single n 1

@[simp]
theorem l1Norm_one : l1Norm (1 : SignedLaw ℝ) = 1 := l1Norm_atom 0

@[simp]
theorem l1Norm_scalar (r : ℝ) : l1Norm (scalar r) = |r| := by
  exact l1Norm_single 0 r

theorem l1Norm_eq_sum_of_support_subset (ν : SignedLaw ℝ) (s : Finset ℕ)
    (hs : ν.coeff.support ⊆ s) : l1Norm ν = ∑ k ∈ s, |ν.coeff k| := by
  exact Finsupp.sum_of_support_subset _ hs _ (fun _ _ => abs_zero)

theorem l1Norm_add (μ ν : SignedLaw ℝ) : l1Norm (μ + ν) ≤ l1Norm μ + l1Norm ν := by
  classical
  let s := μ.coeff.support ∪ ν.coeff.support
  have hμ : μ.coeff.support ⊆ s := Finset.subset_union_left
  have hν : ν.coeff.support ⊆ s := Finset.subset_union_right
  have hsum : (μ + ν).coeff.support ⊆ s := by
    rw [AddMonoidAlgebra.coeff_add]
    exact Finsupp.support_add
  rw [l1Norm_eq_sum_of_support_subset (μ + ν) s hsum,
    l1Norm_eq_sum_of_support_subset μ s hμ, l1Norm_eq_sum_of_support_subset ν s hν,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  exact abs_add_le _ _

@[simp]
theorem l1Norm_neg (ν : SignedLaw ℝ) : l1Norm (-ν) = l1Norm ν := by
  simp [l1Norm, AddMonoidAlgebra.coeff_neg, Finsupp.sum]

theorem l1Norm_sub (μ ν : SignedLaw ℝ) : l1Norm (μ - ν) ≤ l1Norm μ + l1Norm ν := by
  simpa only [sub_eq_add_neg, l1Norm_neg] using l1Norm_add μ (-ν)

theorem l1Norm_sum {ι : Type*} (s : Finset ι) (f : ι → SignedLaw ℝ) :
    l1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (l1Norm_add _ _).trans (add_le_add_right ih _)

theorem l1Norm_mul (μ ν : SignedLaw ℝ) : l1Norm (μ * ν) ≤ l1Norm μ * l1Norm ν := by
  classical
  rw [AddMonoidAlgebra.mul_def]
  change l1Norm (∑ i ∈ μ.coeff.support,
    ∑ j ∈ ν.coeff.support, AddMonoidAlgebra.single (i + j) (μ.coeff i * ν.coeff j)) ≤ _
  calc
    _ ≤ ∑ i ∈ μ.coeff.support,
        l1Norm (∑ j ∈ ν.coeff.support,
          AddMonoidAlgebra.single (i + j) (μ.coeff i * ν.coeff j)) := l1Norm_sum _ _
    _ ≤ ∑ i ∈ μ.coeff.support, ∑ j ∈ ν.coeff.support,
        |μ.coeff i * ν.coeff j| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [l1Norm_single] using l1Norm_sum ν.coeff.support
        (fun j => AddMonoidAlgebra.single (i + j) (μ.coeff i * ν.coeff j))
    _ = l1Norm μ * l1Norm ν := by
      simp only [abs_mul, l1Norm, Finsupp.sum, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm

theorem l1Norm_pow (ν : SignedLaw ℝ) (n : ℕ) : l1Norm (ν ^ n) ≤ l1Norm ν ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    change l1Norm (atom 0 : SignedLaw ℝ) ≤ 1
    rw [l1Norm_atom]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (l1Norm_mul _ _).trans (mul_le_mul_of_nonneg_right ih (l1Norm_nonneg ν))

theorem l1Norm_forwardDifference_le_two : l1Norm (forwardDifference : SignedLaw ℝ) ≤ 2 := by
  calc
    _ ≤ (1 : ℝ) + 1 := by
      simpa only [forwardDifference, l1Norm_atom] using
        l1Norm_sub (atom 1 : SignedLaw ℝ) (atom 0)
    _ = 2 := by ring1

theorem l1Norm_forwardDifference_pow_le (n : ℕ) :
    l1Norm ((forwardDifference : SignedLaw ℝ) ^ n) ≤ (2 : ℝ) ^ n := by
  exact (l1Norm_pow _ n).trans
    (pow_le_pow_left₀ (l1Norm_nonneg _) l1Norm_forwardDifference_le_two n)

/-- Positive kernels cost only their mass in the ordinary ℓ¹ norm. -/
theorem l1Norm_eq_totalMass_of_nonneg (ν : SignedLaw ℝ) (hν : ∀ k, 0 ≤ ν.coeff k) :
    l1Norm ν = totalMass ν := by
  rw [totalMass_eq_sum_coeff]
  unfold l1Norm Finsupp.sum
  apply Finset.sum_congr rfl
  intro k _
  exact abs_of_nonneg (hν k)

theorem l1Norm_probability {ν : SignedLaw ℝ} (hν : IsProbability ν) : l1Norm ν = 1 :=
  (l1Norm_eq_totalMass_of_nonneg ν hν.1).trans hν.2

end PaperP1.Probability
