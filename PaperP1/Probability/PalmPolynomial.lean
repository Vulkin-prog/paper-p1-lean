module

public import PaperP1.Probability.ConditionalPalm
public import PaperP1.Probability.FactorialGeneratingPolynomial

/-! # Exact signed Palm coefficients in powers of z-1

The transform is proved to be the ordinary generating polynomial evaluated
at 1+t. Coefficients are summed with their signs before any norm is taken.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PalmPolynomial

open PaperP1.Algebra PaperP1.Probability PaperP1.IndicatorDeletion PaperP1.FiniteSignedPalm
  PaperP1.FactorialGeneratingPolynomial Polynomial Finset

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]

theorem active_jointMoment (w : Ω → ℝ) (J : ι → Ω → Bool) (x : ι)
    (A : Finset ι) (hx : x ∉ A) :
    jointMoment (fun ω ↦ w ω * indicatorValue (J x ω)) J A = jointMoment w J (insert x A) := by
  unfold jointMoment finiteExpectation
  simp only [prod_insert hx]
  apply sum_congr rfl
  intro ω _
  ring

theorem transform_activeLaw_coeff (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool)
    (x : ι) (j : ℕ) :
    (transform (activeLaw G w J x)).coeff j =
      ∑ A ∈ (G.erase x).powersetCard j, jointMoment w J (insert x A) := by
  rw [activeLaw, transform_countLaw_subset_coeff]
  apply sum_congr rfl
  intro A hA
  apply active_jointMoment
  intro hx
  exact (mem_erase.mp ((mem_powersetCard.mp hA).1 hx)).1 rfl

omit [Fintype Ω] in
theorem powersetCard_erase_filter (G : Finset ι) (x : ι) (j : ℕ) :
    (G.erase x).powersetCard j = (G.powersetCard j).filter (fun A ↦ x ∉ A) := by
  ext A
  simp only [mem_powersetCard, mem_filter]
  constructor
  · rintro ⟨hA, hc⟩
    refine ⟨⟨hA.trans (erase_subset _ _), hc⟩, ?_⟩
    intro hx
    exact (mem_erase.mp (hA hx)).1 rfl
  · rintro ⟨⟨hA, hc⟩, hx⟩
    refine ⟨?_, hc⟩
    intro y hy
    exact mem_erase.mpr ⟨fun hyx ↦ hx (hyx ▸ hy), hA hy⟩

omit [Fintype Ω] in
theorem sum_erased_subsets (G : Finset ι) (j : ℕ) (f : ι → Finset ι → ℝ) :
    (∑ x ∈ G, ∑ A ∈ (G.erase x).powersetCard j, f x A) =
      ∑ A ∈ G.powersetCard j, ∑ x ∈ G \ A, f x A := by
  simp_rw [powersetCard_erase_filter, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  have hf : G.filter (fun x ↦ x ∉ A) = G \ A := by ext x; simp
  rw [← hf, sum_filter]

theorem palm_coefficient (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (j : ℕ) :
    (transform (palmDifference G P J)).coeff j =
      ∑ A ∈ G.powersetCard j, ∑ x ∈ G \ A,
        (jointMoment P.weight J (insert x A) - exactMarginal P J x * jointMoment P.weight J A) := by
  unfold palmDifference
  simp only [map_sum, Polynomial.finsetSum_coeff, map_sub, Polynomial.coeff_sub, map_mul,
    transform_scalar, Polynomial.coeff_C_mul, transform_activeLaw_coeff,
    transform_countLaw_subset_coeff, mul_sum, ← sum_sub_distrib]
  exact sum_erased_subsets G j _

omit [Fintype Ω] [DecidableEq ι] in
theorem count_polynomial_product (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) :
    (1 + X : ℝ[X]) ^ indicatorCount G J ω =
      ∏ x ∈ G, (1 + X * C (indicatorValue (J x ω))) := by
  rw [indicatorCount, ← prod_pow_eq_pow_sum]
  apply prod_congr rfl
  intro x _
  cases J x ω <;> simp [indicatorValue]

omit [Fintype Ω] in
theorem derivative_count_polynomial (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) :
    derivative ((1 + X : ℝ[X]) ^ indicatorCount G J ω) =
      ∑ x ∈ G, C (indicatorValue (J x ω)) * (1 + X) ^ indicatorCount (G.erase x) J ω := by
  rw [count_polynomial_product, derivative_prod_finset]
  apply sum_congr rfl
  intro x _
  rw [← count_polynomial_product]
  simp only [derivative_add, derivative_one, derivative_mul, derivative_X, derivative_C,
    zero_add, one_mul, mul_zero, add_zero]
  exact mul_comm _ _

theorem derivative_transform_countLaw (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool) :
    derivative (transform (countLaw G w J)) = ∑ x ∈ G, transform (activeLaw G w J x) := by
  rw [transform_countLaw, derivative_sum]
  simp_rw [derivative_C_mul, derivative_count_polynomial, mul_sum, activeLaw, transform_countLaw]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro ω _
  rw [map_mul]
  ring

theorem transform_deleted_sum (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool) :
    (∑ x ∈ G, transform (countLaw (G.erase x) w J)) =
      C (G.card : ℝ) * transform (countLaw G w J) -
        X * derivative (transform (countLaw G w J)) := by
  have h := congrArg transform (deleted_law_sum_identity G w J)
  simp only [map_add, map_sum, map_mul, transform_scalar, transform_forwardDifference,
    ← derivative_transform_countLaw] at h
  exact eq_sub_of_add_eq h

theorem uniform_palm_polynomial (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (p : ℝ) (hp : ∀ x ∈ G, exactMarginal P J x = p) :
    transform (palmDifference G P J) = derivative (transform (countLaw G P.weight J)) -
      C p * (C (G.card : ℝ) * transform (countLaw G P.weight J) -
        X * derivative (transform (countLaw G P.weight J))) := by
  calc
    _ = ∑ x ∈ G, (transform (activeLaw G P.weight J x) -
        C p * transform (countLaw (G.erase x) P.weight J)) := by
      unfold palmDifference
      rw [map_sum]
      apply sum_congr rfl
      intro x hx
      rw [map_sub, map_mul, transform_scalar, hp x hx]
    _ = derivative (transform (countLaw G P.weight J)) -
        C p * ∑ x ∈ G, transform (countLaw (G.erase x) P.weight J) := by
      rw [sum_sub_distrib, ← mul_sum, derivative_transform_countLaw]
    _ = _ := by rw [transform_deleted_sum]

omit [Fintype Ω] [DecidableEq ι] in
theorem coeff_X_mul_derivative (F : ℝ[X]) (j : ℕ) :
    (X * derivative F).coeff j = (j : ℝ) * F.coeff j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
    push_cast
    ring

theorem uniform_palm_coefficient (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (p : ℝ) (hp : ∀ x ∈ G, exactMarginal P J x = p) (j : ℕ) :
    (transform (palmDifference G P J)).coeff j =
      (j + 1 : ℝ) * finiteExpectation P.weight (fun ω ↦ ((indicatorCount G J ω).choose (j + 1) : ℝ)) -
        p * ((G.card : ℝ) - j) *
          finiteExpectation P.weight (fun ω ↦ ((indicatorCount G J ω).choose j : ℝ)) := by
  rw [uniform_palm_polynomial G P J p hp]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_derivative,
    coeff_X_mul_derivative, transform_countLaw_coeff]
  ring

end PaperP1.PalmPolynomial
