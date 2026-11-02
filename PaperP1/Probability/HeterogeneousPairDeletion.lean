module

public import PaperP1.Probability.HeterogeneousBernoulli

/-! # Removing an actual pair of heterogeneous Bernoulli factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeterogeneousPairDeletion

open Finset PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson
  PaperP1.HeterogeneousBernoulli

variable {ι : Type*} [DecidableEq ι]

theorem norm_one_sub_bernoulli_le {p : ℝ} (hp : 0 ≤ p) :
    ‖1 - ofFinite (bernoulli p)‖ ≤ 2 * p := by
  rw [CompletedBinomial.bernoulli_eq,
    show 1 - (1 + p • delta) = -(p • delta) by abel, norm_neg]
  exact CompletedBinomial.norm_parameter_le hp

theorem norm_one_sub_pair (e : Finset ι) (p : ι → ℝ) (he : e.card = 2)
    (hp : ∀ i ∈ e, 0 ≤ p i ∧ p i ≤ 1) :
    ‖1 - base e p‖ ≤ 2 * ∑ i ∈ e, p i := by
  obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp he
  have hpi := hp i (mem_insert_self _ _)
  have hpj := hp j (mem_insert_of_mem (mem_singleton_self _))
  let a := ofFinite (bernoulli (p i))
  let b := ofFinite (bernoulli (p j))
  have ha : ‖a‖ ≤ 1 := by
    rw [show ‖a‖ = l1Norm (bernoulli (p i)) from norm_ofFinite _]
    exact (l1Norm_probability (bernoulli_isProbability hpi.1 hpi.2)).le
  have hi : ‖1 - a‖ ≤ 2 * p i := norm_one_sub_bernoulli_le hpi.1
  have hj : ‖1 - b‖ ≤ 2 * p j := norm_one_sub_bernoulli_le hpj.1
  simp only [base, prod_pair hij, map_mul, sum_pair hij]
  change ‖1 - a * b‖ ≤ 2 * (p i + p j)
  rw [show 1 - a * b = (1 - a) + a * (1 - b) by ring]
  calc
    _ ≤ ‖1 - a‖ + ‖a‖ * ‖1 - b‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))
    _ ≤ 2 * p i + 1 * (2 * p j) := add_le_add hi (mul_le_mul ha hj (norm_nonneg _) (by norm_num))
    _ = _ := by ring

theorem base_factorization (G e : Finset ι) (p : ι → ℝ) (hsub : e ⊆ G) :
    base (G \ e) p * base e p = base G p := by
  simpa only [base, map_mul] using congrArg ofFinite
    (prod_sdiff (f := fun i ↦ bernoulli (p i)) hsub)

theorem deletion_error (G e : Finset ι) (p : ι → ℝ) (hsub : e ⊆ G) (he : e.card = 2)
    (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1) {P : ℝ} (hcap : ∀ i ∈ G, p i ≤ P) :
    ‖base (G \ e) p - base G p‖ ≤ 4 * P := by
  have houtside : ‖base (G \ e) p‖ ≤ 1 := norm_base_le_one _ p (fun i hi ↦ hp i (sdiff_subset hi))
  have hpair := norm_one_sub_pair e p he (fun i hi ↦ hp i (hsub hi))
  have hsum : (∑ i ∈ e, p i) ≤ 2 * P := by
    calc
      _ ≤ ∑ _i ∈ e, P := sum_le_sum (fun i hi ↦ hcap i (hsub hi))
      _ = _ := by simp only [sum_const, he, nsmul_eq_mul, Nat.cast_ofNat]
  rw [← base_factorization G e p hsub,
    show base (G \ e) p - base (G \ e) p * base e p = base (G \ e) p * (1 - base e p) by ring]
  have h := (norm_mul_le _ _).trans (mul_le_mul houtside hpair (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
  nlinarith only [h, hsum]

theorem omitted_pair_error (G e : Finset ι) (p : ι → ℝ) (hsub : e ⊆ G) (he : e.card = 2)
    (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1) {P M : ℝ} (hP : 0 ≤ P)
    (hcap : ∀ i ∈ G, p i ≤ P) (hmean : mean G p ≤ M) :
    ‖base (G \ e) p - poisson (mean G p)‖ ≤
      4 * (powerSum G p 2 + P) * Real.exp (2 * M) := by
  have hM : 0 ≤ M := (mean_nonneg G p (fun i hi ↦ (hp i hi).1)).trans hmean
  have hscale := mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity : 0 ≤ 2 * M))
    (by positivity : 0 ≤ 4 * P)
  have htriangle : ‖base (G \ e) p - poisson (mean G p)‖ ≤
      ‖base (G \ e) p - base G p‖ + ‖base G p - poisson (mean G p)‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le
      (base (G \ e) p - base G p) (base G p - poisson (mean G p))
  have h := htriangle.trans (add_le_add (deletion_error G e p hsub he hp hcap)
    (first_order_error G p (fun i hi ↦ (hp i hi).1) hmean))
  nlinarith only [h, hscale]

end PaperP1.HeterogeneousPairDeletion
