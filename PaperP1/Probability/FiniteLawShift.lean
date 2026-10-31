module

public import PaperP1.Probability.L1Norm
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

/-! # Translation is an exact isometry for the ordinary finite ℓ¹ norm -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteLawShift

open PaperP1.Probability

def succEmbedding : ℕ ↪ ℕ := ⟨fun k ↦ 1 + k, fun _ _ h ↦ Nat.add_left_cancel h⟩

def extendedCoefficient (ν : SignedLaw ℝ) (k : ℤ) : ℝ := if 0 ≤ k then ν.coeff k.toNat else 0

@[simp] theorem extendedCoefficient_nat (ν : SignedLaw ℝ) (k : ℕ) :
    extendedCoefficient ν k = ν.coeff k := by simp [extendedCoefficient]

theorem scalar_mul_coeff (c : ℝ) (ν : SignedLaw ℝ) (k : ℕ) :
    (scalar c * ν).coeff k = c * ν.coeff k :=
  AddMonoidAlgebra.coeff_single_zero_mul ν c k

theorem shift_coeff_zero (ν : SignedLaw ℝ) : (atom 1 * ν).coeff 0 = 0 := by
  exact AddMonoidAlgebra.coeff_single_mul_of_forall_add_ne 1 ν (by omega)

theorem shift_coeff_succ (ν : SignedLaw ℝ) (k : ℕ) : (atom 1 * ν).coeff (k + 1) = ν.coeff k := by
  simpa only [atom, Nat.add_comm, one_mul] using AddMonoidAlgebra.coeff_single_mul_add ν 1 1 k

theorem shift_coeff_extended (ν : SignedLaw ℝ) (k : ℕ) :
    (atom 1 * ν).coeff k = extendedCoefficient ν ((k : ℤ) - 1) := by
  cases k with
  | zero => simp [shift_coeff_zero, extendedCoefficient]
  | succ k =>
    rw [shift_coeff_succ]
    simp

theorem second_shift_coeff_extended (ν : SignedLaw ℝ) (k : ℕ) :
    ((atom 1) ^ 2 * ν).coeff k = extendedCoefficient ν ((k : ℤ) - 2) := by
  rw [pow_two, mul_assoc]
  cases k with
  | zero => simp [shift_coeff_zero, extendedCoefficient]
  | succ k =>
    rw [shift_coeff_succ]
    cases k with
    | zero => simp [shift_coeff_zero, extendedCoefficient]
    | succ k =>
      rw [shift_coeff_succ]
      have heq : ((k + 1 + 1 : ℕ) : ℤ) - 2 = (k : ℤ) := by omega
      rw [heq, extendedCoefficient_nat]

theorem shift_coeff_embedding (ν : SignedLaw ℝ) :
    (atom 1 * ν).coeff = ν.coeff.embDomain succEmbedding := by
  ext k
  cases k with
  | zero =>
    rw [shift_coeff_zero, Finsupp.embDomain_of_notMem_range]
    change ¬ ∃ k : ℕ, 1 + k = 0
    omega
  | succ k =>
    rw [shift_coeff_succ]
    rw [Nat.add_comm k 1]
    change ν.coeff k = ν.coeff.embDomain succEmbedding (succEmbedding k)
    rw [Finsupp.embDomain_apply_self]

theorem l1Norm_shift (ν : SignedLaw ℝ) : l1Norm (atom 1 * ν) = l1Norm ν := by
  unfold l1Norm
  rw [shift_coeff_embedding, Finsupp.sum_embDomain]

theorem l1Norm_sub_comm (μ ν : SignedLaw ℝ) : l1Norm (μ - ν) = l1Norm (ν - μ) := by
  rw [← l1Norm_neg (ν - μ), neg_sub]

theorem abs_l1Norm_sub_le (μ ν : SignedLaw ℝ) :
    |l1Norm μ - l1Norm ν| ≤ l1Norm (μ - ν) := by
  apply abs_le.mpr
  constructor
  · have h := l1Norm_add (ν - μ) μ
    rw [sub_add_cancel, l1Norm_sub_comm ν μ] at h
    linarith
  · have h := l1Norm_add (μ - ν) ν
    rw [sub_add_cancel] at h
    linarith

end PaperP1.FiniteLawShift
