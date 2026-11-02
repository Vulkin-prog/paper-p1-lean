module

public import PaperP1.Probability.HeterogeneousPairDeletion

/-! # The complete finite heterogeneous analytic conversion with signed pair weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeterogeneousPoissonCharlierConversion

open Finset PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson
  PaperP1.CompletedLawShift PaperP1.HeterogeneousBernoulli PaperP1.HeterogeneousPairDeletion

variable {ι : Type*} [DecidableEq ι]

def covarianceSum (E : Finset (Finset ι)) (c : Finset ι → ℝ) : ℝ := ∑ e ∈ E, c e

def absolutePairMass (E : Finset (Finset ι)) (c : Finset ι → ℝ) : ℝ := ∑ e ∈ E, |c e|

def finiteReference (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (c : Finset ι → ℝ) : SignedLaw ℝ :=
  (∏ i ∈ G, bernoulli (p i)) +
    ∑ e ∈ E, scalar (c e) * forwardDifference ^ 2 * ∏ i ∈ G \ e, bernoulli (p i)

def completedReference (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (c : Finset ι → ℝ) : Space :=
  base G p + ∑ e ∈ E, c e • (delta ^ 2 * base (G \ e) p)

theorem ofFinite_reference (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (c : Finset ι → ℝ) :
    ofFinite (finiteReference G E p c) = completedReference G E p c := by
  simp only [finiteReference, completedReference, map_add, map_sum]
  congr 1
  apply sum_congr rfl
  intro e _
  rw [mul_assoc, FinitePoissonCharlierConversion.ofFinite_scalar_mul, map_mul, map_pow]
  rfl

theorem coeff_completedReference (G : Finset ι) (E : Finset (Finset ι))
    (p : ι → ℝ) (c : Finset ι → ℝ) (k : ℕ) :
    coeff k (completedReference G E p c) = (finiteReference G E p c).coeff k := by
  rw [← ofFinite_reference, coeff_ofFinite]

theorem covariance_identity (G : Finset ι) (E : Finset (Finset ι))
    (p : ι → ℝ) (c : Finset ι → ℝ) :
    completedReference G E p c - quadratic (mean G p) (2 * covarianceSum E c - powerSum G p 2) =
      (base G p - quadratic (mean G p) (-powerSum G p 2)) +
        ∑ e ∈ E, c e • (delta ^ 2 * (base (G \ e) p - poisson (mean G p))) := by
  simp only [completedReference, quadratic, mul_sub, smul_sub, sum_sub_distrib, ← sum_smul]
  dsimp only [covarianceSum]
  module

theorem norm_pair_error (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (c : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1)
    {P M : ℝ} (hP : 0 ≤ P) (hcap : ∀ i ∈ G, p i ≤ P) (hmean : mean G p ≤ M) :
    ‖∑ e ∈ E, c e • (delta ^ 2 * (base (G \ e) p - poisson (mean G p)))‖ ≤
      16 * Real.exp (2 * M) * absolutePairMass E c * (powerSum G p 2 + P) := by
  have hs₂ := powerSum_nonneg G p (fun i hi ↦ (hp i hi).1) 2
  calc
    _ ≤ ∑ e ∈ E, ‖c e • (delta ^ 2 * (base (G \ e) p - poisson (mean G p)))‖ := norm_sum_le _ _
    _ ≤ ∑ e ∈ E, 16 * Real.exp (2 * M) * |c e| * (powerSum G p 2 + P) := by
      apply sum_le_sum
      intro e he
      rw [norm_smul, Real.norm_eq_abs]
      calc
        _ ≤ |c e| * (‖delta ^ 2‖ * ‖base (G \ e) p - poisson (mean G p)‖) := by
          gcongr
          exact norm_mul_le _ _
        _ ≤ |c e| * (4 * (4 * (powerSum G p 2 + P) * Real.exp (2 * M))) := by
          gcongr
          · exact FinitePoissonCharlierConversion.norm_delta_squared_le
          · exact omitted_pair_error G e p (hE e he).1 (hE e he).2 hp hP hcap hmean
        _ = _ := by ring
    _ = _ := by
      simp only [absolutePairMass, sum_mul, mul_sum]

def constant (M : ℝ) : ℝ := 16 * Real.exp (2 * M)

theorem constant_pos (M : ℝ) : 0 < constant M := by unfold constant; positivity

theorem norm_conversion (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (c : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1)
    {P M : ℝ} (hP : 0 ≤ P) (hcap : ∀ i ∈ G, p i ≤ P) (hmean : mean G p ≤ M) :
    ‖completedReference G E p c - quadratic (mean G p) (2 * covarianceSum E c - powerSum G p 2)‖ ≤
      constant M * (powerSum G p 3 + (powerSum G p 2) ^ 2 + absolutePairMass E c * (powerSum G p 2 + P)) := by
  rw [covariance_identity]
  have h := (norm_add_le _ _).trans (add_le_add
    (quadratic_error G p (fun i hi ↦ (hp i hi).1) hmean)
    (norm_pair_error G E p c hE hp hP hcap hmean))
  convert h using 1; dsimp only [constant]; ring

theorem coefficient_conversion (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (c : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1)
    {P M : ℝ} (hP : 0 ≤ P) (hcap : ∀ i ∈ G, p i ≤ P) (hmean : mean G p ≤ M) :
    (∑' k : ℕ, |(finiteReference G E p c).coeff k -
      PoissonSequence.quadraticMass (mean G p) (2 * covarianceSum E c - powerSum G p 2) k|) ≤
      constant M * (powerSum G p 3 + (powerSum G p 2) ^ 2 + absolutePairMass E c * (powerSum G p 2 + P)) := by
  have h := (tsum_abs_coeff_le (completedReference G E p c -
    quadratic (mean G p) (2 * covarianceSum E c - powerSum G p 2))).trans
      (norm_conversion G E p c hE hp hP hcap hmean)
  simpa only [map_sub, coeff_completedReference, coeff_quadratic] using h

theorem actual_signed_measure_conversion (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (c : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1)
    {P M : ℝ} (hP : 0 ≤ P) (hcap : ∀ i ∈ G, p i ≤ P) (hmean : mean G p ≤ M) :
    (∑' k : ℕ, |(FiniteLawEmbedding.embed (finiteReference G E p c) -
      QuadraticPoisson.reference (mean G p) (2 * covarianceSum E c - powerSum G p 2)) {k}|) ≤
      constant M * (powerSum G p 3 + (powerSum G p 2) ^ 2 + absolutePairMass E c * (powerSum G p 2 + P)) := by
  have hμ := mean_nonneg G p (fun i hi ↦ (hp i hi).1)
  have href (k : ℕ) : QuadraticPoisson.reference (mean G p)
      (2 * covarianceSum E c - powerSum G p 2) {k} =
      PoissonSequence.quadraticMass (mean G p) (2 * covarianceSum E c - powerSum G p 2) k :=
    AtomicSignedLaw.ofSequence_singleton (PoissonSequence.hasSum_quadraticMass _ _ hμ).summable k
  simpa only [_root_.sub_apply, FiniteLawEmbedding.embed_singleton, href] using
    coefficient_conversion G E p c hE hp hP hcap hmean

end PaperP1.HeterogeneousPoissonCharlierConversion
