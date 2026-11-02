module

public import PaperP1.Analysis.ContractiveExponentialProducts
public import PaperP1.Probability.HeterogeneousPoissonCharlierConversion
public import PaperP1.Probability.JumpPoissonSeries

/-! # A universal Poisson–Charlier conversion constant, with no mean bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniversalHeterogeneousConversion

open Finset PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson
  PaperP1.CompletedLawShift PaperP1.HeterogeneousBernoulli PaperP1.HeterogeneousPairDeletion
  PaperP1.HeterogeneousPoissonCharlierConversion

variable {ι : Type*} [DecidableEq ι]

def universalConstant : ℝ := 16 * Real.exp 2

theorem universalConstant_pos : 0 < universalConstant := by unfold universalConstant; positivity

theorem factor_bounds {p : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1) :
    ‖1 + p • delta‖ ≤ 1 ∧ ‖NormedSpace.exp (p • delta)‖ ≤ 1 ∧ ‖p • delta‖ ≤ 2 := by
  have hB : ‖1 + p • delta‖ = 1 := by
    rw [← CompletedBinomial.bernoulli_eq, norm_ofFinite]
    exact l1Norm_probability (bernoulli_isProbability hp hp₁)
  have hD : ‖NormedSpace.exp (p • delta)‖ = 1 := JumpPoissonSeries.norm_poisson hp
  have hR : ‖p • delta‖ ≤ 2 := (CompletedBinomial.norm_parameter_le hp).trans (by linarith)
  exact ⟨hB.le, hD.le, hR⟩

omit [DecidableEq ι] in
theorem first_order_error (G : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1) :
    ‖base G p - poisson (mean G p)‖ ≤ 4 * Real.exp 2 * powerSum G p 2 := by
  have h := ContractiveExponentialProducts.norm_first_order_le G (fun i ↦ p i • delta) 2
    (fun i hi ↦ (factor_bounds (hp i hi).1 (hp i hi).2).1)
    (fun i hi ↦ (factor_bounds (hp i hi).1 (hp i hi).2).2.1)
    (fun i hi ↦ (factor_bounds (hp i hi).1 (hp i hi).2).2.2)
  rw [← base_eq_product, exponentialProduct_eq_poisson] at h
  have h₂ : (∑ i ∈ G, ‖p i • delta‖ ^ 2) ≤ 4 * powerSum G p 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
      norm_power_sum_le G p (fun i hi ↦ (hp i hi).1) 2
  have hbound := h.trans (mul_le_mul_of_nonneg_right h₂ (Real.exp_pos 2).le)
  convert hbound using 1; ring

omit [DecidableEq ι] in
theorem quadratic_error (G : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1) :
    ‖base G p - quadratic (mean G p) (-powerSum G p 2)‖ ≤
      universalConstant * (powerSum G p 3 + (powerSum G p 2) ^ 2) := by
  have h := ContractiveExponentialProducts.norm_quadratic_error_le G (fun i ↦ p i • delta) 2
    (fun i hi ↦ (factor_bounds (hp i hi).1 (hp i hi).2).1)
    (fun i hi ↦ (factor_bounds (hp i hi).1 (hp i hi).2).2.1)
    (fun i hi ↦ (factor_bounds (hp i hi).1 (hp i hi).2).2.2)
  rw [← base_eq_product, exponentialProduct_eq_poisson, quadraticCorrection_eq, smul_mul_assoc] at h
  have hid : base G p - quadratic (mean G p) (-powerSum G p 2) =
      base G p - poisson (mean G p) + (powerSum G p 2 / 2) • (delta ^ 2 * poisson (mean G p)) := by
    simp only [quadratic, neg_div, neg_smul]
    module
  rw [hid]
  have hpos₂ := powerSum_nonneg G p (fun i hi ↦ (hp i hi).1) 2
  have hpos₃ := powerSum_nonneg G p (fun i hi ↦ (hp i hi).1) 3
  have h₂ := norm_power_sum_le G p (fun i hi ↦ (hp i hi).1) 2
  have h₃ := norm_power_sum_le G p (fun i hi ↦ (hp i hi).1) 3
  calc
    _ ≤ (2 * (∑ i ∈ G, ‖p i • delta‖ ^ 3) + (∑ i ∈ G, ‖p i • delta‖ ^ 2) ^ 2) * Real.exp 2 := h
    _ ≤ (2 * ((2 : ℝ) ^ 3 * powerSum G p 3) + ((2 : ℝ) ^ 2 * powerSum G p 2) ^ 2) * Real.exp 2 := by gcongr
    _ = _ := by unfold universalConstant; ring

theorem omitted_pair_error (G e : Finset ι) (p : ι → ℝ) (hsub : e ⊆ G) (he : e.card = 2)
    (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1) {P : ℝ} (hP : 0 ≤ P) (hcap : ∀ i ∈ G, p i ≤ P) :
    ‖base (G \ e) p - poisson (mean G p)‖ ≤ 4 * Real.exp 2 * (powerSum G p 2 + P) := by
  have hscale := mul_le_mul_of_nonneg_left (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity : 0 ≤ 4 * P)
  have htriangle : ‖base (G \ e) p - poisson (mean G p)‖ ≤
      ‖base (G \ e) p - base G p‖ + ‖base G p - poisson (mean G p)‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le
      (base (G \ e) p - base G p) (base G p - poisson (mean G p))
  have h := htriangle.trans (add_le_add (deletion_error G e p hsub he hp hcap) (first_order_error G p hp))
  nlinarith only [h, hscale]

theorem norm_pair_error (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (c : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1)
    {P : ℝ} (hP : 0 ≤ P) (hcap : ∀ i ∈ G, p i ≤ P) :
    ‖∑ e ∈ E, c e • (delta ^ 2 * (base (G \ e) p - poisson (mean G p)))‖ ≤
      universalConstant * absolutePairMass E c * (powerSum G p 2 + P) := by
  have hs₂ := powerSum_nonneg G p (fun i hi ↦ (hp i hi).1) 2
  calc
    _ ≤ ∑ e ∈ E, ‖c e • (delta ^ 2 * (base (G \ e) p - poisson (mean G p)))‖ := norm_sum_le _ _
    _ ≤ ∑ e ∈ E, universalConstant * |c e| * (powerSum G p 2 + P) := by
      apply sum_le_sum
      intro e he
      rw [norm_smul, Real.norm_eq_abs]
      calc
        _ ≤ |c e| * (‖delta ^ 2‖ * ‖base (G \ e) p - poisson (mean G p)‖) := by
          gcongr
          exact norm_mul_le _ _
        _ ≤ |c e| * (4 * (4 * Real.exp 2 * (powerSum G p 2 + P))) := by
          gcongr
          · exact FinitePoissonCharlierConversion.norm_delta_squared_le
          · exact omitted_pair_error G e p (hE e he).1 (hE e he).2 hp hP hcap
        _ = _ := by unfold universalConstant; ring
    _ = _ := by simp only [absolutePairMass, sum_mul, mul_sum]

theorem norm_conversion (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (c : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1)
    {P : ℝ} (hP : 0 ≤ P) (hcap : ∀ i ∈ G, p i ≤ P) :
    ‖completedReference G E p c - quadratic (mean G p) (2 * covarianceSum E c - powerSum G p 2)‖ ≤
      universalConstant * (powerSum G p 3 + (powerSum G p 2) ^ 2 + absolutePairMass E c * (powerSum G p 2 + P)) := by
  rw [covariance_identity]
  have h := (norm_add_le _ _).trans (add_le_add (quadratic_error G p hp) (norm_pair_error G E p c hE hp hP hcap))
  convert h using 1; ring

theorem actual_signed_measure_conversion (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (c : Finset ι → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1)
    {P : ℝ} (hP : 0 ≤ P) (hcap : ∀ i ∈ G, p i ≤ P) :
    (∑' k : ℕ, |(FiniteLawEmbedding.embed (finiteReference G E p c) -
      QuadraticPoisson.reference (mean G p) (2 * covarianceSum E c - powerSum G p 2)) {k}|) ≤
      universalConstant * (powerSum G p 3 + (powerSum G p 2) ^ 2 + absolutePairMass E c * (powerSum G p 2 + P)) := by
  have hμ := mean_nonneg G p (fun i hi ↦ (hp i hi).1)
  have href (k : ℕ) : QuadraticPoisson.reference (mean G p) (2 * covarianceSum E c - powerSum G p 2) {k} =
      PoissonSequence.quadraticMass (mean G p) (2 * covarianceSum E c - powerSum G p 2) k :=
    AtomicSignedLaw.ofSequence_singleton (PoissonSequence.hasSum_quadraticMass _ _ hμ).summable k
  have h := (tsum_abs_coeff_le (completedReference G E p c -
    quadratic (mean G p) (2 * covarianceSum E c - powerSum G p 2))).trans
      (norm_conversion G E p c hE hp hP hcap)
  simpa only [map_sub, coeff_completedReference, coeff_quadratic,
    _root_.sub_apply, FiniteLawEmbedding.embed_singleton, href] using h

end PaperP1.UniversalHeterogeneousConversion
