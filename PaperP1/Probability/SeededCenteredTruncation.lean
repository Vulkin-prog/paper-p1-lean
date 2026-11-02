module

public import PaperP1.Probability.SeedProductBound
public import PaperP1.Probability.CenteredZeroMarginal
public import PaperP1.Probability.StoppedFiniteLaw
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Centered families containing a two-site seed admit a finite moment truncation

The actual seed expectation is q(e)+3*prod p. The remaining estimate uses
only a higher moment of the positive count envelope, with no conditional
independence or positive seed probability premise.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeededCenteredTruncation

open Finset PaperP1.Algebra PaperP1.Probability

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]

def positiveProduct (J : ι → Ω → Bool) (p : ι → ℝ) (I : Finset ι) (ω : Ω) : ℝ :=
  ∏ x ∈ I, ((indicatorValue (J x ω) : ℝ) + p x)

omit [DecidableEq ι] in
theorem centered_le_positive (P : FiniteProbability Ω) (J : ι → Ω → Bool) (p : ι → ℝ)
    (hp : ∀ x, 0 ≤ p x) (I : Finset ι) :
    |centeredMoment P.weight (fun x ω ↦ (indicatorValue (J x ω) : ℝ)) p I| ≤
      finiteExpectation P.weight (positiveProduct J p I) := by
  unfold centeredMoment finiteExpectation positiveProduct
  calc
    _ ≤ ∑ ω, |P.weight ω * ∏ x ∈ I, ((indicatorValue (J x ω) : ℝ) - p x)| := abs_sum_le_sum_abs _ _
    _ = ∑ ω, P.weight ω * ∏ x ∈ I, |(indicatorValue (J x ω) : ℝ) - p x| := by
      apply sum_congr rfl
      intro ω _
      rw [abs_mul, abs_of_nonneg (P.weight_nonneg ω), abs_prod]
    _ ≤ _ := by
      apply sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (P.weight_nonneg ω)
      apply prod_le_prod₀ (fun _ _ ↦ abs_nonneg _)
      intro x _
      have hJ : (0 : ℝ) ≤ indicatorValue (J x ω) := by cases J x ω <;> norm_num [indicatorValue]
      simpa only [abs_of_nonneg hJ, abs_of_nonneg (hp x)] using
        abs_sub (indicatorValue (J x ω) : ℝ) (p x)

theorem pair_positive_mean (P : FiniteProbability Ω) (J : ι → Ω → Bool) (p : ι → ℝ)
    (e : Finset ι) (he : e.card = 2) (hmean : ∀ x ∈ e, exactMarginal P J x = p x) :
    finiteExpectation P.weight (positiveProduct J p e) = finiteJointMoment P J e + 3 * ∏ x ∈ e, p x := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp he
  unfold positiveProduct finiteJointMoment
  simp only [prod_pair hxy]
  calc
    _ = finiteExpectation P.weight (fun ω ↦
      (indicatorValue (J x ω) : ℝ) * indicatorValue (J y ω) +
        p x * indicatorValue (J y ω) + p y * indicatorValue (J x ω) + p x * p y) := by
      congr 1
      funext ω
      ring
    _ = _ := by
      rw [finiteExpectation_add, finiteExpectation_add, finiteExpectation_add,
        finiteExpectation_const_mul, finiteExpectation_const_mul, finiteExpectation_const,
        P.total_weight, one_mul]
      change _ + p x * exactMarginal P J y + p y * exactMarginal P J x + p x * p y = _
      rw [hmean x (mem_insert_self _ _), hmean y (mem_insert_of_mem (mem_singleton_self _))]
      ring

theorem pointwise_truncation (G : Finset ι) (w : ι → ℝ) (hw : ∀ x, 0 ≤ w x)
    (r : ℕ) (hr : 2 ≤ r) (F T : Finset (Finset ι))
    (hF : ∀ e ∈ F, e ⊆ G ∧ e.card = 2)
    (hT : ∀ I ∈ T, I ⊆ G ∧ I.card = r ∧ ∃ e ∈ F, e ⊆ I)
    (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : r ≤ m) :
    (∑ I ∈ T, ∏ x ∈ I, w x) ≤
      R ^ (r - 2) * (∑ e ∈ F, ∏ x ∈ e, w x) +
        (∑ x ∈ G, w x) ^ m / R ^ (m - r) := by
  let X := ∑ x ∈ G, w x
  let S := ∑ e ∈ F, ∏ x ∈ e, w x
  have hX : 0 ≤ X := sum_nonneg fun x _ ↦ hw x
  have hS : 0 ≤ S := sum_nonneg fun e _ ↦ prod_nonneg fun x _ ↦ hw x
  have hFsub : F ⊆ G.powersetCard 2 := fun e he ↦ mem_powersetCard.mpr (hF e he)
  have hS2 : S ≤ X ^ 2 := by
    have hle : S ≤ X ^ 2 / 2 :=
      (sum_le_sum_of_subset_of_nonneg hFsub (fun e _ _ ↦ prod_nonneg fun x _ ↦ hw x)).trans
        (ElementarySymmetricBound.elementary_le_power_div w hw G 2)
    nlinarith only [hle, sq_nonneg X]
  have hcover : ∀ I ∈ T, I ⊆ G ∧ I.card = 2 + (r - 2) ∧ ∃ e ∈ F, e ⊆ I := by
    intro I hI
    exact ⟨(hT I hI).1, by have h := (hT I hI).2.1; omega, (hT I hI).2.2⟩
  have hseed : (∑ I ∈ T, ∏ x ∈ I, w x) ≤ S * X ^ (r - 2) := by
    have hfac : (1 : ℝ) ≤ (r - 2).factorial := by exact_mod_cast Nat.factorial_pos (r - 2)
    exact (SeedProductBound.power_bound G w hw 2 (r - 2) F T hF hcover).trans
      (mul_le_mul_of_nonneg_left (div_le_self (pow_nonneg hX _) hfac) hS)
  change _ ≤ R ^ (r - 2) * S + X ^ m / R ^ (m - r)
  by_cases hXR : X ≤ R
  · have hpow := pow_le_pow_left₀ hX hXR (r - 2)
    have hb := mul_le_mul_of_nonneg_left hpow hS
    have ht : 0 ≤ X ^ m / R ^ (m - r) := by positivity
    nlinarith only [hseed, hb, ht]
  · have hRX : R ≤ X := (lt_of_not_ge hXR).le
    have hrpow : X ^ r ≤ X ^ m / R ^ (m - r) := by
      apply (le_div_iff₀ (pow_pos hR _)).mpr
      calc
        _ ≤ X ^ r * X ^ (m - r) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRX _) (pow_nonneg hX _)
        _ = _ := by rw [← pow_add, show r + (m - r) = m by omega]
    have hupper : (∑ I ∈ T, ∏ x ∈ I, w x) ≤ X ^ r := by
      calc
        _ ≤ S * X ^ (r - 2) := hseed
        _ ≤ X ^ 2 * X ^ (r - 2) := mul_le_mul_of_nonneg_right hS2 (pow_nonneg hX _)
        _ = _ := by rw [← pow_add, show 2 + (r - 2) = r by omega]
    have hfirst : 0 ≤ R ^ (r - 2) * S := by positivity
    linarith only [hupper, hrpow, hfirst]

theorem finite_bound (P : FiniteProbability Ω) (J : ι → Ω → Bool) (p : ι → ℝ)
    (hp : ∀ x, 0 ≤ p x) (G : Finset ι) (hmean : ∀ x ∈ G, exactMarginal P J x = p x)
    (r : ℕ) (hr : 2 ≤ r) (F T : Finset (Finset ι))
    (hF : ∀ e ∈ F, e ⊆ G ∧ e.card = 2)
    (hT : ∀ I ∈ T, I ⊆ G ∧ I.card = r ∧ ∃ e ∈ F, e ⊆ I)
    (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : r ≤ m) :
    (∑ I ∈ T, |centeredMoment P.weight (fun x ω ↦ (indicatorValue (J x ω) : ℝ)) p I|) ≤
      R ^ (r - 2) * (∑ e ∈ F, (finiteJointMoment P J e + 3 * ∏ x ∈ e, p x)) +
      finiteExpectation P.weight (fun ω ↦ (∑ x ∈ G, ((indicatorValue (J x ω) : ℝ) + p x)) ^ m) /
        R ^ (m - r) := by
  have hnonneg (ω : Ω) (x : ι) : 0 ≤ (indicatorValue (J x ω) : ℝ) + p x := by
    cases J x ω <;> norm_num [indicatorValue] <;> linarith only [hp x]
  have hseed : finiteExpectation P.weight (fun ω ↦ ∑ e ∈ F, positiveProduct J p e ω) =
      ∑ e ∈ F, (finiteJointMoment P J e + 3 * ∏ x ∈ e, p x) := by
    rw [finiteExpectation_sum]
    apply sum_congr rfl
    intro e he
    exact pair_positive_mean P J p e (hF e he).2 (fun x hx ↦ hmean x ((hF e he).1 hx))
  have hdiv : finiteExpectation P.weight (fun ω ↦
      (∑ x ∈ G, ((indicatorValue (J x ω) : ℝ) + p x)) ^ m / R ^ (m - r)) =
      finiteExpectation P.weight (fun ω ↦ (∑ x ∈ G, ((indicatorValue (J x ω) : ℝ) + p x)) ^ m) / R ^ (m - r) := by
    simp only [div_eq_mul_inv, finiteExpectation_mul_const]
  calc
    _ ≤ ∑ I ∈ T, finiteExpectation P.weight (positiveProduct J p I) :=
      sum_le_sum fun I _ ↦ centered_le_positive P J p hp I
    _ = finiteExpectation P.weight (fun ω ↦ ∑ I ∈ T, positiveProduct J p I ω) :=
      (finiteExpectation_sum P.weight T (fun I ω ↦ positiveProduct J p I ω)).symm
    _ ≤ finiteExpectation P.weight (fun ω ↦
      R ^ (r - 2) * (∑ e ∈ F, positiveProduct J p e ω) +
        (∑ x ∈ G, ((indicatorValue (J x ω) : ℝ) + p x)) ^ m / R ^ (m - r)) := by
      apply sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left
        (pointwise_truncation G (fun x ↦ (indicatorValue (J x ω) : ℝ) + p x)
          (hnonneg ω) r hr F T hF hT R hR m hm) (P.weight_nonneg ω)
    _ = _ := by rw [finiteExpectation_add, finiteExpectation_const_mul, hseed, hdiv]

end PaperP1.SeededCenteredTruncation
