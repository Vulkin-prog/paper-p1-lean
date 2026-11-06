module

public import PaperP1.Analysis.FullEulerUnit
public import PaperP1.Analysis.UnitThickening
public import PaperP1.Analysis.CommonUnitException
public import PaperP1.Analysis.ReciprocalFrequencyWeights
public import PaperP1.Analysis.FullEulerBound
public import PaperP1.Analysis.PrimeUnitMean
set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FullEulerEnvelope
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

def exceptional (N K : ℕ) : Set ℝ :=
  UnitThickening.thickening K (CommonUnitException.badUnits N K)

theorem exceptional_measurable (N K : ℕ) : MeasurableSet (exceptional N K) :=
  UnitThickening.thickening_measurable K _

theorem exceptional_measure (N K : ℕ) : volume.real (exceptional N K) ≤ 2*((CommonUnitException.badUnits N K).card : ℝ) :=
  UnitThickening.thickening_measure K _

theorem off_exception_norm (N X : ℕ) (hN : 1 ≤ N) (hX : 2 ≤ X) (hNX : N ≤ X) (δ : ℝ) (hδ : 0 < δ)
    (hH : 8*(FullEulerBound.harmonicConstant+1-Real.log δ) ≤ PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N))
    (K : ℕ) (u : ℝ) (hu : u ∈ Set.Icc (-(K : ℝ)) (K : ℝ)) (hnot : u ∉ exceptional N K)
    (f : ℕ → ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (t : ℝ) (ht : t ∈ Set.Icc (u-1/2) (u+1/2)) :
    ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖ ≤ δ*Real.log (X : ℝ) := by
  obtain ⟨j,hj,hgood,hjt⟩ := UnitThickening.good_unit_at_point K (CommonUnitException.badUnits N K) u hu hnot t ht
  exact FullEulerUnit.off_bad_unit_norm N X hN hX hNX δ hδ hH K j hj hgood f hf t hjt

theorem shifted_local_sup_bound (N X : ℕ) (hN : 1 ≤ N) (hX : 2 ≤ X) (hNX : N ≤ X) (δ : ℝ) (hδ : 0 < δ)
    (hH : 8*(FullEulerBound.harmonicConstant+1-Real.log δ) ≤ PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N))
    (K : ℕ) (h τ : ℝ) (hu : h+τ ∈ Set.Icc (-(K : ℝ)) (K : ℝ))
    (f : ℕ → ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) :
    PrimeUnitMean.localSquareSup (fun t ↦ RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (t+τ)) h ≤
      (Real.log (X : ℝ))^2*(δ^2+FullEulerBound.eulerConstant^2*(exceptional N K).indicator (fun _ ↦ (1 : ℝ)) (h+τ)) := by
  have hF : Continuous (fun t : ℝ ↦ RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (t+τ)) :=
    (FullEulerUnit.full_continuous X f hf).comp (continuous_id.add continuous_const)
  obtain ⟨t,ht,he⟩ := PrimeUnitMean.local_sup_attained _ hF h
  rw [he]
  by_cases hex : h+τ ∈ exceptional N K
  · rw [Set.indicator_of_mem hex]
    have hh := pow_le_pow_left₀ (norm_nonneg _) (FullEulerBound.global_bound X hX f hf (t+τ)) 2
    rw [mul_pow] at hh
    nlinarith [sq_nonneg δ,mul_nonneg (sq_nonneg (Real.log (X : ℝ))) (sq_nonneg δ)]
  · rw [Set.indicator_of_notMem hex]
    have ht' : t+τ ∈ Set.Icc (h+τ-1/2) (h+τ+1/2) := by constructor <;> linarith [ht.1,ht.2]
    have hb := off_exception_norm N X hN hX hNX δ hδ hH K (h+τ) hu hex f hf (t+τ) ht'
    have hh := pow_le_pow_left₀ (norm_nonneg _) hb 2
    simpa only [mul_zero,add_zero,mul_pow,mul_comm] using hh

def badWeight (N K M : ℕ) (τ : ℝ) : ℝ :=
  ∑ j ∈ range (2*M+1), (exceptional N K).indicator (fun _ ↦ (1 : ℝ)) ((j : ℝ)-(M : ℝ)+τ)/
    (1+((j : ℝ)-(M : ℝ))^2)

theorem badWeight_nonneg (N K M : ℕ) (τ : ℝ) : 0 ≤ badWeight N K M τ := by
  apply sum_nonneg
  intro j hj
  exact div_nonneg (Set.indicator_nonneg (fun _ _ ↦ by norm_num) _) (by positivity)



theorem badWeight_le_five (N K M : ℕ) (τ : ℝ) : badWeight N K M τ ≤ 5 := by
  calc
    _ ≤ ∑ j ∈ range (2*M+1), 1/(1+((j : ℝ)-(M : ℝ))^2) := by
      apply sum_le_sum
      intro j hj
      apply div_le_div_of_nonneg_right _ (by positivity)
      by_cases he : (j : ℝ)-(M : ℝ)+τ ∈ exceptional N K
      · simpa only [Set.indicator_of_mem he] using (le_rfl : (1 : ℝ) ≤ 1)
      · simpa only [Set.indicator_of_notMem he] using (zero_le_one : (0 : ℝ) ≤ 1)
    _ ≤ _ := ReciprocalFrequencyWeights.finite_weight_bound _ _

theorem shifted_budget_envelope (N X : ℕ) (hN : 1 ≤ N) (hX : 2 ≤ X) (hNX : N ≤ X) (δ : ℝ) (hδ : 0 < δ)
    (hH : 8*(FullEulerBound.harmonicConstant+1-Real.log δ) ≤ PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N))
    (K M : ℕ) (T : ℝ) (hcover : T+(M : ℝ) ≤ (K : ℝ)) (τ : ℝ) (hτ : τ ∈ Set.Icc (-T) T)
    (f : ℕ → ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) :
    PrimeUnitMean.frequencyBudget (fun t ↦ RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (t+τ)) M ≤
      (Real.log (X : ℝ))^2*(5*δ^2+FullEulerBound.eulerConstant^2*badWeight N K M τ) := by
  have hweight := ReciprocalFrequencyWeights.finite_weight_bound (range (2*M+1)) M
  calc
    _ ≤ ∑ j ∈ range (2*M+1), (Real.log (X : ℝ))^2*
        (δ^2+FullEulerBound.eulerConstant^2*(exceptional N K).indicator (fun _ ↦ (1 : ℝ)) ((j : ℝ)-(M : ℝ)+τ))/
          (1+((j : ℝ)-(M : ℝ))^2) := by
      apply sum_le_sum
      intro j hj
      have hjN : j ≤ 2*M := by have hh := mem_range.mp hj; omega
      have hjR : (j : ℝ) ≤ 2*(M : ℝ) := by exact_mod_cast hjN
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact shifted_local_sup_bound N X hN hX hNX δ hδ hH K ((j : ℝ)-(M : ℝ)) τ
        (by constructor <;> linarith [hτ.1,hτ.2]) f hf
    _ = (Real.log (X : ℝ))^2*(δ^2*(∑ j ∈ range (2*M+1), 1/(1+((j : ℝ)-(M : ℝ))^2))+
        FullEulerBound.eulerConstant^2*badWeight N K M τ) := by
      dsimp only [badWeight]
      simp only [mul_add,mul_sum]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hweight (sq_nonneg δ)) (le_rfl : FullEulerBound.eulerConstant^2*badWeight N K M τ ≤ _))
        (sq_nonneg (Real.log (X : ℝ)))
      simpa only [mul_comm (δ^2) 5] using hh
end PaperP1.FullEulerEnvelope
