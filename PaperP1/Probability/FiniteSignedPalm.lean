module

public import PaperP1.Probability.IndicatorDeletion
public import PaperP1.Probability.FiniteLawShift
public import PaperP1.Probability.FiniteLawEmbedding

/-! # The signed Palm residual with its exact heterogeneous diagonal error

All sources are summed before taking the norm. The active source law is
unnormalized here; the next bridge identifies it with the actual conditional
law multiplied by its own marginal, including the zero-marginal convention.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteSignedPalm

open PaperP1.Algebra PaperP1.Probability PaperP1.IndicatorDeletion PaperP1.FiniteLawShift
  PaperP1.FiniteLawEmbedding Finset

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]

def mean (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool) : ℝ :=
  finiteExpectation P.weight (fun ω ↦ (indicatorCount G J ω : ℝ))

def palmDifference (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool) : SignedLaw ℝ :=
  ∑ x ∈ G, (activeLaw G P.weight J x - scalar (exactMarginal P J x) *
    countLaw (G.erase x) P.weight J)

def diagonalError (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool) : SignedLaw ℝ :=
  ∑ x ∈ G, scalar (exactMarginal P J x) *
    (countLaw (G.erase x) P.weight J - countLaw G P.weight J)

def residualLaw (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool) (θ : ℝ) : SignedLaw ℝ :=
  sizeWeightedLaw G P.weight J - scalar (mean G P J - θ) * atom 1 * countLaw G P.weight J -
    scalar θ * (atom 1) ^ 2 * countLaw G P.weight J

def recurrenceNorm (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool) (θ : ℝ) : ℝ :=
  l1Norm (residualLaw G P J θ)

omit [DecidableEq ι] in
theorem residualLaw_coeff (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (θ : ℝ) (k : ℕ) :
    (residualLaw G P J θ).coeff k = (k : ℝ) * (countLaw G P.weight J).coeff k -
      (mean G P J - θ) * extendedCoefficient (countLaw G P.weight J) ((k : ℤ) - 1) -
        θ * extendedCoefficient (countLaw G P.weight J) ((k : ℤ) - 2) := by
  simp only [residualLaw, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, sizeWeightedLaw_coeff]
  rw [mul_assoc (scalar (mean G P J - θ)), mul_assoc (scalar θ), scalar_mul_coeff,
    scalar_mul_coeff, shift_coeff_extended, second_shift_coeff_extended]

omit [DecidableEq ι] in
theorem recurrenceNorm_eq_tsum (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (θ : ℝ) :
    recurrenceNorm G P J θ = ∑' k : ℕ, |(k : ℝ) * (countLaw G P.weight J).coeff k -
      (mean G P J - θ) * extendedCoefficient (countLaw G P.weight J) ((k : ℤ) - 1) -
        θ * extendedCoefficient (countLaw G P.weight J) ((k : ℤ) - 2)| := by
  rw [recurrenceNorm, l1Norm_eq_tsum]
  apply tsum_congr
  intro k
  rw [residualLaw_coeff]

theorem palm_add_diagonal (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool) :
    palmDifference G P J + diagonalError G P J =
      (∑ x ∈ G, activeLaw G P.weight J x) - scalar (mean G P J) * countLaw G P.weight J := by
  unfold palmDifference diagonalError
  rw [← sum_add_distrib]
  calc
    _ = ∑ x ∈ G, (activeLaw G P.weight J x - scalar (exactMarginal P J x) *
        countLaw G P.weight J) := by
      apply sum_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [sum_sub_distrib, ← sum_mul, ← map_sum, mean, mean_indicatorCount]

theorem residualLaw_eq_shift (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (θ : ℝ) :
    residualLaw G P J θ = atom 1 * (palmDifference G P J + diagonalError G P J -
      scalar θ * forwardDifference * countLaw G P.weight J) := by
  rw [palm_add_diagonal]
  unfold residualLaw forwardDifference
  rw [sizeWeightedLaw_eq_shift_active, map_sub, atom_zero]
  ring

theorem deletion_l1_bound {G : Finset ι} {x : ι} (hx : x ∈ G)
    (P : FiniteProbability Ω) (J : ι → Ω → Bool) :
    l1Norm (countLaw (G.erase x) P.weight J - countLaw G P.weight J) ≤ 2 * exactMarginal P J x := by
  have h := countLaw_subset_coupling P (erase_subset x G) J
  rw [sdiff_erase_self hx, sum_singleton, lawTotalVariation] at h
  rw [l1Norm_sub_comm]
  linarith

theorem diagonalError_l1_bound (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) :
    l1Norm (diagonalError G P J) ≤ 2 * ∑ x ∈ G, (exactMarginal P J x) ^ 2 := by
  unfold diagonalError
  calc
    _ ≤ ∑ x ∈ G, l1Norm (scalar (exactMarginal P J x) *
        (countLaw (G.erase x) P.weight J - countLaw G P.weight J)) := l1Norm_sum _ _
    _ ≤ ∑ x ∈ G, 2 * (exactMarginal P J x) ^ 2 := by
      apply sum_le_sum
      intro x hx
      have hp := exactMarginal_nonneg P J x
      calc
        _ ≤ l1Norm (scalar (exactMarginal P J x)) *
            l1Norm (countLaw (G.erase x) P.weight J - countLaw G P.weight J) := l1Norm_mul _ _
        _ = exactMarginal P J x *
            l1Norm (countLaw (G.erase x) P.weight J - countLaw G P.weight J) := by
          rw [l1Norm_scalar, abs_of_nonneg hp]
        _ ≤ exactMarginal P J x * (2 * exactMarginal P J x) :=
          mul_le_mul_of_nonneg_left (deletion_l1_bound hx P J) hp
        _ = _ := by ring
    _ = _ := (mul_sum G _ 2).symm

theorem signed_palm_residual_bound (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (θ : ℝ) :
    |recurrenceNorm G P J θ - l1Norm (palmDifference G P J -
      scalar θ * forwardDifference * countLaw G P.weight J)| ≤
        2 * ∑ x ∈ G, (exactMarginal P J x) ^ 2 := by
  unfold recurrenceNorm
  rw [residualLaw_eq_shift, l1Norm_shift]
  have h := abs_l1Norm_sub_le
    (palmDifference G P J + diagonalError G P J - scalar θ * forwardDifference * countLaw G P.weight J)
    (palmDifference G P J - scalar θ * forwardDifference * countLaw G P.weight J)
  have heq : (palmDifference G P J + diagonalError G P J -
      scalar θ * forwardDifference * countLaw G P.weight J) -
      (palmDifference G P J - scalar θ * forwardDifference * countLaw G P.weight J) =
        diagonalError G P J := by ring
  rw [heq] at h
  exact h.trans (diagonalError_l1_bound G P J)

end PaperP1.FiniteSignedPalm
