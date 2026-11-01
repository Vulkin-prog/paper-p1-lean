module

public import PaperP1.Model.ConditionalCountMean
public import PaperP1.Arithmetic.WindowPoolCount
public import PaperP1.Algebra.ExponentialSupportSlope

/-! # A finite conditional-mean bound with the exact binary incidence slope -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConditionalRunBudget

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.ConditionalRunRank
  PaperP1.ConditionalRunProbability PaperP1.ConditionalWindowRank PaperP1.ConditionalCountMean
  PaperP1.WindowPoolCount PaperP1.ExponentialSupportSlope

def largeStarts (N L : ℕ) (R O : Finset ℕ) (T : ℕ) : Finset ℕ :=
  (dyadicBlock N \ O).filter fun x ↦ T < (supportedIndices R (x - 1) (L + 1)).card

theorem conditionalStartProbability_le_one {M x L : ℕ} {R : Finset ℕ}
    (hL : 0 < L) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M) :
    conditionalStartProbability R a x L ≤ 1 := by
  rw [conditionalStartProbability_eq_affine hL hcut hR]
  exact conditionalAffineMass_le_one _ _ _ _

theorem conditionalStartProbability_le_pow {M x L : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hL : 0 < L) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M) :
    conditionalStartProbability R a x L ≤
      (2 : ℝ) ^ ((supportedIndices R (x - 1) (L + 1)).card - 1) / (2 ^ L : ℝ) := by
  rcases conditionalStartProbability_zero_or_pow hx hL hcut hR a with hzero | hpow
  · rw [hzero]
    positivity
  · rw [hpow]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) (conditionalNullity_le R (x - 1) (L + 1))) (by positivity)

theorem conditionalStartProbability_le_incidence {M x L T : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hL : 0 < L) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M)
    (hcount : (supportedIndices R (x - 1) (L + 1)).card ≤ T) :
    conditionalStartProbability R a x L ≤ (2 ^ L : ℝ)⁻¹ +
      (2 ^ L : ℝ)⁻¹ * slope T * (supportedIndices R (x - 1) (L + 1)).card := by
  let t := (supportedIndices R (x - 1) (L + 1)).card
  have hp : (0 : ℝ) ≤ (2 ^ L : ℝ)⁻¹ := by positivity
  by_cases ht : t ≤ 1
  · rw [conditionalStartProbability_nominal hx hL hcut hR a ht]
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hp (slope_nonneg T)) (Nat.cast_nonneg t))
  · have hpow := conditionalStartProbability_le_pow hx hL hcut hR a
    have hloss := loss_le_slope (by omega : 1 ≤ t) hcount
    have hmul := mul_le_mul_of_nonneg_left hloss hp
    rw [div_eq_mul_inv] at hpow
    dsimp [t] at hmul
    nlinarith

theorem conditional_count_bound_sharp {M N L T : ℕ} {R O : Finset ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLN : L ≤ N) (hcut : 2 * N + L ≤ M)
    (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M) (hO : O ⊆ dyadicBlock N) :
    conditionalCountExpectation R a (dyadicBlock N) L ≤
      (N : ℝ) * (2 ^ L : ℝ)⁻¹ + O.card + (largeStarts N L R O T).card +
        (2 ^ L : ℝ)⁻¹ * slope T * (L + 1) * (poolValues R (L + 1) (3 * N)).card := by
  let p : ℝ := (2 ^ L : ℝ)⁻¹
  let D := largeStarts N L R O T
  have hpoint (x : ℕ) (hx : x ∈ dyadicBlock N) :
      conditionalStartProbability R a x L ≤ p + (if x ∈ O then (1 : ℝ) else 0) +
        (if x ∈ D then (1 : ℝ) else 0) + p * slope T * (supportedIndices R (x - 1) (L + 1)).card := by
    have hxb := mem_Ico.mp hx
    have hxM : x + L ≤ M := by omega
    have hbound := conditionalStartProbability_le_one hL hxM hR a
    have hrest : 0 ≤ p * slope T * (supportedIndices R (x - 1) (L + 1)).card :=
      mul_nonneg (mul_nonneg (by positivity) (slope_nonneg T)) (Nat.cast_nonneg _)
    by_cases hxO : x ∈ O
    · simp only [hxO, ite_true]
      split_ifs <;> dsimp [p] at * <;> linarith [show (0 : ℝ) ≤ (2 ^ L : ℝ)⁻¹ by positivity]
    · by_cases hxD : x ∈ D
      · simp only [hxO, hxD, ite_false, ite_true]
        dsimp [p] at *
        linarith [show (0 : ℝ) ≤ (2 ^ L : ℝ)⁻¹ by positivity]
      · have hcount : (supportedIndices R (x - 1) (L + 1)).card ≤ T := by
          by_contra h
          exact hxD (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hx, hxO⟩, by omega⟩)
        simpa only [hxO, hxD, ite_false, add_zero] using
          conditionalStartProbability_le_incidence (by omega) hL hxM hR a hcount
  have hcardO : (∑ x ∈ dyadicBlock N, if x ∈ O then (1 : ℝ) else 0) = O.card := by
    rw [← sum_filter]
    have heq : (dyadicBlock N).filter (fun x ↦ x ∈ O) = O := by
      ext x
      exact ⟨fun h ↦ (mem_filter.mp h).2, fun h ↦ mem_filter.mpr ⟨hO h, h⟩⟩
    rw [heq]
    simp
  have hD : D ⊆ dyadicBlock N := (filter_subset _ _).trans sdiff_subset
  have hcardD : (∑ x ∈ dyadicBlock N, if x ∈ D then (1 : ℝ) else 0) = D.card := by
    rw [← sum_filter]
    have heq : (dyadicBlock N).filter (fun x ↦ x ∈ D) = D := by
      ext x
      exact ⟨fun h ↦ (mem_filter.mp h).2, fun h ↦ mem_filter.mpr ⟨hD h, h⟩⟩
    rw [heq]
    simp
  have hsum := sum_le_sum hpoint
  have htotal : ((∑ x ∈ dyadicBlock N, (supportedIndices R (x - 1) (L + 1)).card : ℕ) : ℝ) ≤
      ((L + 1) * (poolValues R (L + 1) (3 * N)).card : ℕ) := by
    exact_mod_cast sum_supportedIndices_dyadic (R := R) hN hLN
  rw [conditionalCountExpectation_eq_sum hL (fun x hx ↦ by have h := (mem_Ico.mp hx).2; omega) hR a]
  simp only [sum_add_distrib, hcardO, hcardD, sum_const, nsmul_eq_mul, dyadicBlock_card,
    ← mul_sum] at hsum
  have hinc := mul_le_mul_of_nonneg_left htotal (mul_nonneg (by positivity : 0 ≤ p) (slope_nonneg T))
  push_cast at hinc
  dsimp [p, D] at hsum hinc
  nlinarith

theorem conditional_count_bound {M N L T : ℕ} {R O : Finset ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLN : L ≤ N) (hcut : 2 * N + L ≤ M)
    (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M) (hT : 1 ≤ T) (hO : O ⊆ dyadicBlock N) :
    conditionalCountExpectation R a (dyadicBlock N) L ≤
      (N : ℝ) * (2 ^ L : ℝ)⁻¹ + O.card + (largeStarts N L R O T).card +
        (2 ^ L : ℝ)⁻¹ * (2 : ℝ) ^ (T - 1) * (L + 1) * (poolValues R (L + 1) (3 * N)).card := by
  have h := conditional_count_bound_sharp (T := T) hN hL hLN hcut hR a hO
  have hslope := slope_le_source hT
  have hmul := mul_le_mul_of_nonneg_left hslope
    (show 0 ≤ (2 ^ L : ℝ)⁻¹ * (L + 1) * (poolValues R (L + 1) (3 * N)).card by positivity)
  nlinarith

end PaperP1.ConditionalRunBudget
