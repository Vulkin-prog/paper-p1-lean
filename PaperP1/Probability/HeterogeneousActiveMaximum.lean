module

public import PaperP1.Probability.HereditaryActiveMaximum
public import PaperP1.Algebra.ElementarySymmetricBound

/-! # Every-order bounds for an active maximum with heterogeneous marginal weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeterogeneousActiveMaximum

open Finset PaperP1.Algebra PaperP1.Probability PaperP1.HereditaryActiveMaximum
  PaperP1.SubsetPowerSums

variable {Ω ι : Type*} [Fintype Ω] [LinearOrder ι]

theorem expected_choose_elementary (P : FiniteProbability Ω) (G : Finset ι) (F : Finset (Finset ι))
    (hzero : ∅ ∈ F) (hF : Hereditary F) (hground : ∀ A ∈ F, A ⊆ G)
    (J : ι → Ω → Bool) (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hjoint : ∀ A ∈ F, finiteJointMoment P J A ≤ ∏ x ∈ A, p x) (r : ℕ) :
    finiteExpectation P.weight (fun ω ↦ ((maximumSize F J ω).choose r : ℝ)) ≤ elementary p G r := by
  have hsub : orderFamilies F r ⊆ G.powersetCard r := by
    intro A hA
    obtain ⟨hAF, hcard⟩ := mem_filter.mp hA
    exact mem_powersetCard.mpr ⟨hground A hAF, hcard⟩
  calc
    _ ≤ ∑ A ∈ orderFamilies F r, finiteJointMoment P J A := expected_choose_bound P F hzero hF J r
    _ ≤ ∑ A ∈ orderFamilies F r, ∏ x ∈ A, p x :=
      sum_le_sum fun A hA ↦ hjoint A (mem_filter.mp hA).1
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ ↦ prod_nonneg fun x _ ↦ hp x)

theorem expected_choose_poisson (P : FiniteProbability Ω) (G : Finset ι) (F : Finset (Finset ι))
    (hzero : ∅ ∈ F) (hF : Hereditary F) (hground : ∀ A ∈ F, A ⊆ G)
    (J : ι → Ω → Bool) (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hjoint : ∀ A ∈ F, finiteJointMoment P J A ≤ ∏ x ∈ A, p x) (r : ℕ) :
    finiteExpectation P.weight (fun ω ↦ ((maximumSize F J ω).choose r : ℝ)) ≤
      (∑ x ∈ G, p x) ^ r / (r.factorial : ℝ) :=
  (expected_choose_elementary P G F hzero hF hground J p hp hjoint r).trans
    (ElementarySymmetricBound.elementary_le_power_div p hp G r)

theorem expected_factorial (P : FiniteProbability Ω) (G : Finset ι) (F : Finset (Finset ι))
    (hzero : ∅ ∈ F) (hF : Hereditary F) (hground : ∀ A ∈ F, A ⊆ G)
    (J : ι → Ω → Bool) (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hjoint : ∀ A ∈ F, finiteJointMoment P J A ≤ ∏ x ∈ A, p x) (r : ℕ) :
    finiteExpectation P.weight (fun ω ↦ ((maximumSize F J ω).descFactorial r : ℝ)) ≤
      (∑ x ∈ G, p x) ^ r := by
  have hc := expected_choose_elementary P G F hzero hF hground J p hp hjoint r
  have hid (ω : Ω) : ((maximumSize F J ω).descFactorial r : ℝ) =
      (r.factorial : ℝ) * ((maximumSize F J ω).choose r : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  simp_rw [hid]
  rw [finiteExpectation_const_mul]
  exact (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg r.factorial)).trans
    (ElementarySymmetricBound.factorial_elementary_le p hp G r)

omit [LinearOrder ι] in
theorem expected_power_product (P : FiniteProbability Ω) (G : Finset ι) (F : Finset (Finset ι))
    (hzero : ∅ ∈ F) (hF : Hereditary F) (hground : ∀ A ∈ F, A ⊆ G)
    (J : ι → Ω → Bool) (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hjoint : ∀ A ∈ F, finiteJointMoment P J A ≤ ∏ x ∈ A, p x) (s : ℝ) (hs : 1 ≤ s) :
    finiteExpectation P.weight (fun ω ↦ s ^ maximumSize F J ω) ≤
      ∏ x ∈ G, (1 + (s - 1) * p x) := by
  have hsub : F ⊆ G.powerset := fun A hA ↦ mem_powerset.mpr (hground A hA)
  calc
    _ ≤ finiteExpectation P.weight (fun ω ↦
        ∑ A ∈ F, (s - 1) ^ A.card * ∏ x ∈ A, (indicatorValue (J x ω) : ℝ)) :=
      sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (power_le_active_generator F hzero hF J ω s hs) (P.weight_nonneg ω)
    _ = ∑ A ∈ F, (s - 1) ^ A.card * finiteJointMoment P J A := by
      rw [finiteExpectation_sum]
      apply sum_congr rfl
      intro A _
      exact finiteExpectation_const_mul _ _ _
    _ ≤ ∑ A ∈ F, ∏ x ∈ A, ((s - 1) * p x) := by
      apply sum_le_sum
      intro A hA
      have heq : (s - 1) ^ A.card * (∏ x ∈ A, p x) = ∏ x ∈ A, ((s - 1) * p x) := by
        rw [prod_mul_distrib, prod_const]
      rw [← heq]
      exact mul_le_mul_of_nonneg_left (hjoint A hA) (pow_nonneg (sub_nonneg.mpr hs) _)
    _ ≤ ∑ A ∈ G.powerset, ∏ x ∈ A, ((s - 1) * p x) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ ↦ prod_nonneg fun x _ ↦ mul_nonneg (sub_nonneg.mpr hs) (hp x))
    _ = _ := (prod_one_add (f := fun x ↦ (s - 1) * p x) G).symm

omit [LinearOrder ι] in
theorem expected_power_exponential (P : FiniteProbability Ω) (G : Finset ι) (F : Finset (Finset ι))
    (hzero : ∅ ∈ F) (hF : Hereditary F) (hground : ∀ A ∈ F, A ⊆ G)
    (J : ι → Ω → Bool) (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hjoint : ∀ A ∈ F, finiteJointMoment P J A ≤ ∏ x ∈ A, p x) (s : ℝ) (hs : 1 ≤ s) :
    finiteExpectation P.weight (fun ω ↦ s ^ maximumSize F J ω) ≤
      Real.exp ((s - 1) * ∑ x ∈ G, p x) := by
  calc
    _ ≤ ∏ x ∈ G, (1 + (s - 1) * p x) := expected_power_product P G F hzero hF hground J p hp hjoint s hs
    _ ≤ ∏ x ∈ G, Real.exp ((s - 1) * p x) := by
      apply prod_le_prod₀
      · intro x _
        have h := mul_nonneg (sub_nonneg.mpr hs) (hp x)
        linarith only [h]
      · intro x _
        linarith only [Real.add_one_le_exp ((s - 1) * p x)]
    _ = _ := by rw [← Real.exp_sum, ← mul_sum]

theorem tail_bound (P : FiniteProbability Ω) (G : Finset ι) (F : Finset (Finset ι))
    (hzero : ∅ ∈ F) (hF : Hereditary F) (hground : ∀ A ∈ F, A ⊆ G)
    (J : ι → Ω → Bool) (p : ι → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hjoint : ∀ A ∈ F, finiteJointMoment P J A ≤ ∏ x ∈ A, p x) (r : ℕ) :
    finiteExpectation P.weight (fun ω ↦ if r ≤ maximumSize F J ω then (1 : ℝ) else 0) ≤
      (∑ x ∈ G, p x) ^ r / (r.factorial : ℝ) := by
  apply (le_trans ?_ (expected_choose_poisson P G F hzero hF hground J p hp hjoint r))
  apply sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (P.weight_nonneg ω)
  dsimp only
  split_ifs with h
  · have hpos := Nat.choose_pos h
    exact_mod_cast (show 1 ≤ (maximumSize F J ω).choose r by omega)
  · exact Nat.cast_nonneg _

end PaperP1.HeterogeneousActiveMaximum
