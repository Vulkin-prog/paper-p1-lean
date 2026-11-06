module

public import PaperP1.Analysis.CommonUnitException
public import PaperP1.Analysis.ReciprocalFrequencyWeights
public import PaperP1.Analysis.FullEulerBound
public import PaperP1.Analysis.PrimeUnitMean
set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FullEulerUnit
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

theorem full_continuous (X : ℕ) (f : ℕ → ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) :
    Continuous (RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f) :=
  RealPrimeEulerBound.product_continuous _ (FixedEulerTruncation.primes_prime X) f
    (fun p hp ↦ hf p (FixedEulerTruncation.primes_prime X p hp))

theorem global_unit_sup (X : ℕ) (hX : 2 ≤ X) (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (h : ℝ) :
    PrimeUnitMean.localSquareSup (RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f) h ≤
      (FullEulerBound.eulerConstant*Real.log (X : ℝ))^2 :=
  ReciprocalFrequencyWeights.local_sup_bound _ (full_continuous X f hf) _ (FullEulerBound.global_bound X hX f hf) h

theorem off_bad_unit_norm (N X : ℕ) (hN : 1 ≤ N) (hX : 2 ≤ X) (hNX : N ≤ X)
    (δ : ℝ) (hδ : 0 < δ)
    (hH : 8*(FullEulerBound.harmonicConstant+1-Real.log δ) ≤ PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N))
    (K j : ℕ) (hj : j ∈ range (2*K+1)) (hnot : j ∉ CommonUnitException.badUnits N K)
    (f : ℕ → ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (t : ℝ)
    (ht : t ∈ Set.Icc ((j : ℝ)-(K : ℝ)-1/2) ((j : ℝ)-(K : ℝ)+1/2)) :
    ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖ ≤ δ*Real.log (X : ℝ) := by
  apply FullEulerBound.small_of_distance X hX (SlowPrimeBandSieve.primes N) (FullEulerBound.slow_subset N X hN hNX) f hf t δ hδ
  have hh := CommonUnitException.off_bad_distance N K j hj hnot f
    (fun p hp ↦ hf p (mem_filter.mp hp).2) t ht
  linarith

theorem off_bad_unit_sup (N X : ℕ) (hN : 1 ≤ N) (hX : 2 ≤ X) (hNX : N ≤ X)
    (δ : ℝ) (hδ : 0 < δ)
    (hH : 8*(FullEulerBound.harmonicConstant+1-Real.log δ) ≤ PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N))
    (K j : ℕ) (hj : j ∈ range (2*K+1)) (hnot : j ∉ CommonUnitException.badUnits N K)
    (f : ℕ → ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) :
    PrimeUnitMean.localSquareSup (RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f) ((j : ℝ)-(K : ℝ)) ≤
      δ^2*(Real.log (X : ℝ))^2 := by
  obtain ⟨t,ht,he⟩ := PrimeUnitMean.local_sup_attained _ (full_continuous X f hf) ((j : ℝ)-(K : ℝ))
  rw [he]
  have hb := off_bad_unit_norm N X hN hX hNX δ hδ hH K j hj hnot f hf t ht
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2

theorem shifted_global_budget (X : ℕ) (hX : 2 ≤ X) (f : ℕ → ℝ)
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (τ : ℝ) (K : ℕ) :
    PrimeUnitMean.frequencyBudget (fun t ↦ RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (t+τ)) K ≤
      5*FullEulerBound.eulerConstant^2*(Real.log (X : ℝ))^2 := by
  have hh := ReciprocalFrequencyWeights.frequency_budget_bound
    (fun t ↦ RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (t+τ))
    ((full_continuous X f hf).comp (continuous_id.add continuous_const))
    (FullEulerBound.eulerConstant*Real.log (X : ℝ)) (fun t ↦ FullEulerBound.global_bound X hX f hf (t+τ)) K
  simpa only [mul_pow,mul_assoc] using hh

theorem unit_sup_small_uniform (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ X ≥ N, ∀ K : ℕ, (SlowPrimeBandSieve.upper N)^3 ≤ (K : ℝ) →
      ((CommonUnitException.badUnits N K).card : ℝ) ≤ ε*(2*(K : ℝ)+1) ∧
        ∀ j ∈ range (2*K+1), j ∉ CommonUnitException.badUnits N K → ∀ f : ℕ → ℝ,
          (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
          PrimeUnitMean.localSquareSup (RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f) ((j : ℝ)-(K : ℝ)) ≤
            δ^2*(Real.log (X : ℝ))^2 := by
  obtain ⟨N₁,hN₁,hh⟩ := CommonUnitException.unit_repulsion_small_uniform
    (FullEulerBound.harmonicConstant+1-Real.log δ) ε hε
  refine ⟨max N₁ 2,le_max_right _ _,?_⟩
  intro N hN X hNX K hK
  obtain ⟨hcard,hgood⟩ := hh N (by omega) K hK
  refine ⟨hcard,?_⟩
  intro j hj hnot f hf
  obtain ⟨t,ht,he⟩ := PrimeUnitMean.local_sup_attained _ (full_continuous X f hf) ((j : ℝ)-(K : ℝ))
  rw [he]
  have hD := hgood j hj hnot f (fun p hp ↦ hf p (mem_filter.mp hp).2) t ht
  have hb := FullEulerBound.small_of_distance X (by omega) (SlowPrimeBandSieve.primes N)
    (FullEulerBound.slow_subset N X (by omega) hNX) f hf t δ hδ hD
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2
end PaperP1.FullEulerUnit
