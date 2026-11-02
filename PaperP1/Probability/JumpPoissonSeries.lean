module

public import PaperP1.Probability.CompletedPoisson
public import PaperP1.Probability.PoissonProduct

/-! # Actual jump-Poisson laws as absolutely convergent convolution series -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.JumpPoissonSeries

open MeasureTheory PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson
  PaperP1.PoissonSequence

def generator (j : ℕ) : Space := ofFinite (atom j) - 1

def jumpPoisson (j : ℕ) (μ : ℝ) : Space := NormedSpace.exp (μ • generator j)

theorem atom_pow (j n : ℕ) : (atom j : SignedLaw ℝ) ^ n = atom (j * n) := by
  simp only [atom, AddMonoidAlgebra.single_pow, one_pow, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]

theorem factorization (j : ℕ) (μ : ℝ) :
    jumpPoisson j μ = Real.exp (-μ) • NormedSpace.exp (μ • ofFinite (atom j)) := by
  have hsplit : μ • generator j = algebraMap ℝ Space (-μ) + μ • ofFinite (atom j) := by
    simp only [generator, smul_sub, Algebra.algebraMap_eq_smul_one, neg_smul]
    abel
  rw [jumpPoisson, hsplit, NormedSpace.exp_add, exponential_scalar, smul_mul_assoc, one_mul]

theorem hasSum_jumpPoisson (j : ℕ) (μ : ℝ) :
    HasSum (fun n : ℕ ↦ mass μ n • ofFinite (atom (j * n))) (jumpPoisson j μ) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
    (μ • ofFinite (atom j))).const_smul (Real.exp (-μ))
  rw [← factorization] at h
  convert h using 1
  funext n
  rw [smul_pow, ← map_pow, atom_pow, smul_smul, smul_smul]
  congr 1
  unfold mass
  ring

theorem norm_term (j : ℕ) (μ : ℝ) (n : ℕ) :
    ‖mass μ n • ofFinite (atom (j * n))‖ = |mass μ n| := by
  rw [norm_smul, norm_ofFinite, l1Norm_atom, mul_one, Real.norm_eq_abs]

theorem summable_norm (j : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) :
    Summable (fun n : ℕ ↦ ‖mass μ n • ofFinite (atom (j * n))‖) := by
  simp_rw [norm_term, abs_of_nonneg (PoissonPartialSums.mass_nonneg hμ _)]
  exact (hasSum_mass μ hμ).summable

theorem norm_jumpPoisson_le_one (j : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) : ‖jumpPoisson j μ‖ ≤ 1 := by
  apply (hasSum_jumpPoisson j μ).norm_le_of_bounded (hasSum_mass μ hμ)
  intro n
  rw [norm_term, abs_of_nonneg (PoissonPartialSums.mass_nonneg hμ n)]

theorem coeff_jumpPoisson (j : ℕ) (μ : ℝ) (k : ℕ) :
    coeff k (jumpPoisson j μ) = PushforwardMass.map (fun n : ℕ ↦ j * n) (mass μ) k := by
  have h := (hasSum_jumpPoisson j μ).map (coeff k) (coeff k).continuous
  dsimp only [Function.comp_def] at h
  have heq (n : ℕ) : coeff k (mass μ n • ofFinite (atom (j * n))) =
      if j * n = k then mass μ n else 0 := by
    simp only [map_smul, coeff_ofFinite, atom, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> simp
  simp_rw [heq] at h
  rw [← h.tsum_eq]
  unfold PushforwardMass.map
  change (∑' n : ℕ, if j * n = k then mass μ n else 0) =
    ∑' i : ({n : ℕ | j * n = k} : Set ℕ), mass μ i.val
  rw [tsum_subtype ({n : ℕ | j * n = k} : Set ℕ) (mass μ)]
  apply tsum_congr
  intro n
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

def law (j : ℕ) (μ : ℝ) (hμ : 0 ≤ μ) : ProbabilityMeasure ℕ :=
  PushforwardMass.law (fun n : ℕ ↦ j * n) (mass μ) (PoissonPartialSums.mass_nonneg hμ) (hasSum_mass μ hμ)

theorem actual_signed_measure (j : ℕ) (μ : ℝ) (hμ : 0 ≤ μ) :
    toSignedMeasure (jumpPoisson j μ) = (law j μ hμ : Measure ℕ).toSignedMeasure := by
  rw [law, PushforwardMass.law, AtomicProbability.ofMass_toSignedMeasure]
  unfold toSignedMeasure
  congr 1
  funext k
  exact coeff_jumpPoisson j μ k

theorem norm_jumpPoisson (j : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) : ‖jumpPoisson j μ‖ = 1 := by
  have hsum : (∑' k : ℕ, |coeff k (jumpPoisson j μ)|) = 1 := by
    simp_rw [coeff_jumpPoisson, abs_of_nonneg
      (PushforwardMass.map_nonneg (PoissonPartialSums.mass_nonneg hμ) (fun n : ℕ ↦ j * n) _)]
    exact (PushforwardMass.hasSum_map (hasSum_mass μ hμ) (fun n : ℕ ↦ j * n)).tsum_eq
  exact le_antisymm (norm_jumpPoisson_le_one j hμ)
    (by simpa only [hsum] using tsum_abs_coeff_le (jumpPoisson j μ))

theorem jump_one (μ : ℝ) : jumpPoisson 1 μ = poisson μ := by
  simp only [jumpPoisson, generator, poisson, delta, forwardDifference, map_sub, atom_zero, map_one]

theorem norm_poisson {μ : ℝ} (hμ : 0 ≤ μ) : ‖poisson μ‖ = 1 := by
  rw [← jump_one]
  exact norm_jumpPoisson 1 hμ

end PaperP1.JumpPoissonSeries
