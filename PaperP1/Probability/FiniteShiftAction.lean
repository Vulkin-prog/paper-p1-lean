module

public import PaperP1.Probability.DifferenceCoefficients
public import PaperP1.Probability.FiniteLawShift
public import PaperP1.Probability.PoissonSequence

/-! # Finite convolution kernels act exactly on infinite mass sequences -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteShiftAction

open Finset PaperP1.Probability PaperP1.PoissonSequence

def shiftBy : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, a => a
  | j + 1, a => shift (shiftBy j a)

def shiftLinear : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) where
  toFun := shift
  map_add' a b := by funext k; cases k <;> simp [shift]
  map_smul' c a := by funext k; cases k <;> simp [shift]

def action (a : ℕ → ℝ) (ν : SignedLaw ℝ) : ℕ → ℝ :=
  Finsupp.linearCombination ℝ (fun j ↦ shiftBy j a) ν.coeff

def difference (r : ℕ) (a : ℕ → ℝ) : ℕ → ℝ := action a ((forwardDifference : SignedLaw ℝ) ^ r)

theorem action_sub (a : ℕ → ℝ) (ν κ : SignedLaw ℝ) :
    action a (ν - κ) = action a ν - action a κ := by
  simp only [action, AddMonoidAlgebra.coeff_sub, map_sub]

theorem action_single (a : ℕ → ℝ) (j : ℕ) (c : ℝ) :
    action a (AddMonoidAlgebra.single j c) = c • shiftBy j a := by
  simp only [action, AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_apply,
    Finsupp.sum_single_index, zero_smul]

theorem action_one (a : ℕ → ℝ) : action a 1 = a := by
  change action a (AddMonoidAlgebra.single 0 1) = a
  rw [action_single, one_smul]
  rfl

theorem action_shift (a : ℕ → ℝ) (ν : SignedLaw ℝ) :
    action a (atom 1 * ν) = shift (action a ν) := by
  change action a (atom 1 * ν) = shiftLinear (action a ν)
  simp only [action, Finsupp.linearCombination_apply, PaperP1.FiniteLawShift.shift_coeff_embedding,
    Finsupp.sum_embDomain]
  unfold Finsupp.sum
  rw [map_sum]
  apply sum_congr rfl
  intro j _
  rw [map_smul]
  change _ • shiftBy (1 + j) a = _ • shift (shiftBy j a)
  rw [Nat.add_comm 1 j]
  rfl

theorem action_apply (a : ℕ → ℝ) (ν : SignedLaw ℝ) (k : ℕ) :
    action a ν k = ∑ j ∈ ν.coeff.support, ν.coeff j * shiftBy j a k := by
  simp only [action, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

theorem difference_zero (a : ℕ → ℝ) : difference 0 a = a := by
  simp only [difference, pow_zero, action_one]

theorem difference_succ (r : ℕ) (a : ℕ → ℝ) :
    difference (r + 1) a = shift (difference r a) - difference r a := by
  have hpow : (forwardDifference : SignedLaw ℝ) ^ (r + 1) =
      atom 1 * forwardDifference ^ r - forwardDifference ^ r := by
    rw [pow_succ', forwardDifference, atom_zero, sub_mul, one_mul]
  rw [difference, hpow, action_sub, action_shift]
  rfl

theorem difference_apply_range (r : ℕ) (a : ℕ → ℝ) (k : ℕ) :
    difference r a k = ∑ j ∈ range (r + 1),
      ((forwardDifference : SignedLaw ℝ) ^ r).coeff j * shiftBy j a k := by
  rw [difference, action_apply]
  apply sum_subset (PaperP1.DifferenceCoefficients.support_forwardDifference_pow r)
  intro j _ hj
  rw [Finsupp.notMem_support_iff.mp hj, zero_mul]

theorem shiftBy_at_add (j : ℕ) (a : ℕ → ℝ) (n : ℕ) : shiftBy j a (n + j) = a n := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [shiftBy, Nat.add_succ, shift_succ] using ih

theorem shiftBy_of_lt (j : ℕ) (a : ℕ → ℝ) (k : ℕ) (hk : k < j) : shiftBy j a k = 0 := by
  induction j generalizing k with
  | zero => omega
  | succ j ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k (by omega)

end PaperP1.FiniteShiftAction
