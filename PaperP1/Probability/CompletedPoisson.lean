module

public import PaperP1.Probability.CompletedLaw
public import PaperP1.Probability.PoissonSequence
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # The actual Poisson coefficients of the completed convolution exponential -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompletedPoisson

open PaperP1.Probability PaperP1.CompletedLaw

instance : NormedAlgebra ℚ Space := NormedAlgebra.restrictScalars ℚ ℝ Space

def delta : Space := ofFinite forwardDifference

def poisson (μ : ℝ) : Space := NormedSpace.exp (μ • delta)

theorem atom_one_pow (n : ℕ) : (atom 1 : SignedLaw ℝ) ^ n = atom n := by
  simp only [atom, AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul, mul_one, Nat.cast_id]

theorem coeff_atom_power (n k : ℕ) :
    coeff k ((ofFinite (atom 1)) ^ n) = if n = k then 1 else 0 := by
  rw [← map_pow, atom_one_pow, coeff_ofFinite]
  simp only [atom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem coeff_exponential_atom (μ : ℝ) (k : ℕ) :
    coeff k (NormedSpace.exp (μ • ofFinite (atom 1))) = μ ^ k / (k.factorial : ℝ) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
    (μ • ofFinite (atom 1))).map (coeff k) (coeff k).continuous
  have heq (n : ℕ) : coeff k (((n.factorial : ℝ)⁻¹) •
      (μ • ofFinite (atom 1)) ^ n) =
        if n = k then μ ^ k / (k.factorial : ℝ) else 0 := by
    simp only [map_smul, smul_pow, coeff_atom_power, smul_eq_mul]
    split_ifs with hn
    · subst n; ring
    · ring
  dsimp only [Function.comp_def] at h
  simp_rw [heq] at h
  simpa only [tsum_ite_eq, tsum_zero, add_zero] using h.tsum_eq.symm

theorem exponential_scalar (r : ℝ) :
    NormedSpace.exp (algebraMap ℝ Space r) = Real.exp r • (1 : Space) := by
  rw [← NormedSpace.map_exp (algebraMap ℝ Space) (continuous_algebraMap _ _) r,
    ← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]

theorem poisson_factorization (μ : ℝ) :
    poisson μ = Real.exp (-μ) • NormedSpace.exp (μ • ofFinite (atom 1)) := by
  have hsplit : μ • delta = algebraMap ℝ Space (-μ) + μ • ofFinite (atom 1) := by
    simp only [delta, forwardDifference, map_sub, atom_zero, map_one,
      Algebra.algebraMap_eq_smul_one, neg_smul, smul_sub]
    abel
  rw [poisson, hsplit, NormedSpace.exp_add, exponential_scalar, smul_mul_assoc, one_mul]

theorem coeff_poisson (μ : ℝ) (k : ℕ) : coeff k (poisson μ) = PoissonSequence.mass μ k := by
  rw [poisson_factorization, map_smul, coeff_exponential_atom]
  simp only [PoissonSequence.mass, smul_eq_mul, mul_div_assoc]

theorem poisson_actual_signed_measure (μ : ℝ) :
    toSignedMeasure (poisson μ) = AtomicSignedLaw.ofSequence (PoissonSequence.mass μ) := by
  unfold toSignedMeasure
  congr 1
  funext k
  exact coeff_poisson μ k

theorem poisson_is_probability {μ : ℝ} (hμ : 0 ≤ μ) :
    AtomicSignedLaw.IsProbability (toSignedMeasure (poisson μ)) := by
  rw [poisson_actual_signed_measure]
  apply (AtomicSignedLaw.isProbability_ofSequence_iff (PoissonSequence.hasSum_mass μ hμ)).mpr
  intro k
  unfold PoissonSequence.mass
  positivity

end PaperP1.CompletedPoisson
