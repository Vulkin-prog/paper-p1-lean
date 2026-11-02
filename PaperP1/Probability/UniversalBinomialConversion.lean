module

public import PaperP1.Probability.UniversalHeterogeneousConversion

/-! # The homogeneous pair conversion with the same universal constant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniversalBinomialConversion

open Finset PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson
  PaperP1.CompletedLawShift PaperP1.CompletedBinomial PaperP1.HeterogeneousBernoulli
  PaperP1.UniversalHeterogeneousConversion

theorem covariance_reference_error {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1) (c₂ : ℝ) :
    ‖FinitePoissonCharlierConversion.completedReference n p c₂ -
      quadratic ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2)‖ ≤
      universalConstant * ((n : ℝ) * p ^ 3 + ((n : ℝ) * p ^ 2) ^ 2 + |c₂| * ((n : ℝ) * p ^ 2 + p)) := by
  have hpair : ({0, 1} : Finset ℕ) ⊆ range n := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact mem_range.mpr (by omega)
  have hcard : ((range n) \ ({0, 1} : Finset ℕ)).card = n - 2 := by
    rw [card_sdiff_of_subset hpair, card_range]
    norm_num
  have hbase : base (range n) (fun _ : ℕ ↦ p) = binomial n p := by
    simp only [base, prod_const, card_range, binomial]
  have hother : base ((range n) \ ({0, 1} : Finset ℕ)) (fun _ : ℕ ↦ p) = binomial (n - 2) p := by
    rw [base, prod_const, hcard]
    rfl
  have hE : ∀ e ∈ ({({0, 1} : Finset ℕ)} : Finset (Finset ℕ)), e ⊆ range n ∧ e.card = 2 := by
    intro e he
    have heq := mem_singleton.mp he
    subst e
    exact ⟨hpair, by decide⟩
  have h := UniversalHeterogeneousConversion.norm_conversion (range n) {({0, 1} : Finset ℕ)}
    (fun _ : ℕ ↦ p) (fun _ ↦ c₂) hE (fun _ _ ↦ ⟨hp, hp₁⟩) hp (fun _ _ ↦ le_refl p)
  simp only [HeterogeneousPoissonCharlierConversion.completedReference,
    HeterogeneousPoissonCharlierConversion.covarianceSum,
    HeterogeneousPoissonCharlierConversion.absolutePairMass, mean, powerSum,
    sum_singleton, sum_const, card_range, nsmul_eq_mul, hbase, hother] at h
  simpa only [FinitePoissonCharlierConversion.completedReference, card_singleton, Nat.cast_one, one_mul] using h

theorem reference_lipschitz (n : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1) (β γ : ℝ) :
    ‖FinitePoissonCharlierConversion.completedReference n p β -
      FinitePoissonCharlierConversion.completedReference n p γ‖ ≤ 4 * |β - γ| := by
  have hproduct : ‖delta ^ 2 * binomial (n - 2) p‖ ≤ 4 := by
    exact (norm_mul_le _ _).trans (by simpa only [mul_one] using (mul_le_mul
      FinitePoissonCharlierConversion.norm_delta_squared_le (norm_binomial_le_one (n - 2) hp hp₁)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)))
  have hid : FinitePoissonCharlierConversion.completedReference n p β -
      FinitePoissonCharlierConversion.completedReference n p γ =
        (β - γ) • (delta ^ 2 * binomial (n - 2) p) := by
    unfold FinitePoissonCharlierConversion.completedReference
    module
  rw [hid, norm_smul, Real.norm_eq_abs]
  nlinarith only [mul_le_mul_of_nonneg_left hproduct (abs_nonneg (β - γ))]

theorem norm_conversion {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1) (β c₂ : ℝ) :
    ‖FinitePoissonCharlierConversion.completedReference n p β -
      quadratic ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2)‖ ≤
      4 * |β - c₂| + universalConstant *
        ((n : ℝ) * p ^ 3 + ((n : ℝ) * p ^ 2) ^ 2 + |c₂| * ((n : ℝ) * p ^ 2 + p)) := by
  have htriangle : ‖FinitePoissonCharlierConversion.completedReference n p β -
      quadratic ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2)‖ ≤
      ‖FinitePoissonCharlierConversion.completedReference n p β -
        FinitePoissonCharlierConversion.completedReference n p c₂‖ +
      ‖FinitePoissonCharlierConversion.completedReference n p c₂ -
        quadratic ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2)‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le
      (FinitePoissonCharlierConversion.completedReference n p β -
        FinitePoissonCharlierConversion.completedReference n p c₂)
      (FinitePoissonCharlierConversion.completedReference n p c₂ -
        quadratic ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2))
  exact htriangle.trans (add_le_add (reference_lipschitz n hp hp₁ β c₂) (covariance_reference_error hn hp hp₁ c₂))

theorem actual_signed_measure_conversion {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1) (β c₂ : ℝ) :
    (∑' k : ℕ, |(FiniteLawEmbedding.embed (FinitePoissonCharlierConversion.finiteReference n p β) -
      QuadraticPoisson.reference ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2)) {k}|) ≤
      4 * |β - c₂| + universalConstant *
        ((n : ℝ) * p ^ 3 + ((n : ℝ) * p ^ 2) ^ 2 + |c₂| * ((n : ℝ) * p ^ 2 + p)) := by
  have href (k : ℕ) : QuadraticPoisson.reference ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2) {k} =
      PoissonSequence.quadraticMass ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2) k :=
    AtomicSignedLaw.ofSequence_singleton
      (PoissonSequence.hasSum_quadraticMass _ _ (mul_nonneg (Nat.cast_nonneg n) hp)).summable k
  have h := (tsum_abs_coeff_le (FinitePoissonCharlierConversion.completedReference n p β -
    quadratic ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2))).trans (norm_conversion hn hp hp₁ β c₂)
  simpa only [map_sub, FinitePoissonCharlierConversion.coeff_completedReference, coeff_quadratic,
    _root_.sub_apply, FiniteLawEmbedding.embed_singleton, href] using h

end PaperP1.UniversalBinomialConversion
