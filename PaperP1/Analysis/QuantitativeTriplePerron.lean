module

public import PaperP1.Analysis.GaussianFibreError
public import PaperP1.Analysis.FullTriplePerron

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.QuantitativeTriplePerron
open Finset Nat MeasureTheory PaperP1 Filter FiniteGaussianPerron
open scoped Classical

def error (X : ℕ) : ℝ := GaussianFibreError.errorBound (1/Real.log 2) X (LogarithmicGaussianSum.width X)

theorem finite_bound_eventually :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ f : ℕ → ℂ,
      (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) → ∀ P Q S : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ 2*p ≤ X) → (∀ q ∈ Q, q.Prime) → (∀ n ∈ S, 0 < n) →
      ‖sharp (X : ℝ) (TripleCoefficientFibre.triples P Q S) (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level‖ ≤
        ((X : ℝ)/(2*Real.pi))*(∫ t : ℝ, EulerIntegralLimit.weight ((LogarithmicGaussianSum.width X)^2)
          P (PrimeFactorCauchy.bandCoefficient f (X : ℝ)) Q f t*‖polynomial S f id t‖)+error X := by
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp
    (LogarithmicGaussianSum.width_tendsto.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2)))
  refine ⟨max X₀ 2,le_max_right _ _,?_⟩
  intro X hX f hf P Q S hP hQ hS
  have hX2 : 2 ≤ X := by omega
  have hXP : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hδ := LogarithmicGaussianSum.width_positive X hX2
  have hn := TripleCoefficientFibre.level_pos P Q S (fun p hp ↦ (hP p hp).1) hQ hS
  have he := GaussianFibreError.finite_error_bound (TripleCoefficientFibre.triples P Q S)
    (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level (1/Real.log 2) (by positivity)
    X (by omega) (LogarithmicGaussianSum.width X) hδ (hX₀ X (by omega)).le hn
    (TripleCoefficientFibre.actual_coefficient_fibre_bound f hf X P Q S hP hQ hS)
  have hb := smoothed_norm_bound ((LogarithmicGaussianSum.width X)^2) (X : ℝ) (sq_pos_of_pos hδ) hXP
    (TripleCoefficientFibre.triples P Q S) (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level hn
  have htri : ‖sharp (X : ℝ) (TripleCoefficientFibre.triples P Q S) (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level‖ ≤
      ‖smoothed ((LogarithmicGaussianSum.width X)^2) (X : ℝ) (TripleCoefficientFibre.triples P Q S)
        (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level‖+error X := by
    calc
      _ = ‖smoothed ((LogarithmicGaussianSum.width X)^2) (X : ℝ) (TripleCoefficientFibre.triples P Q S)
          (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level-
        (smoothed ((LogarithmicGaussianSum.width X)^2) (X : ℝ) (TripleCoefficientFibre.triples P Q S)
          (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level-
          sharp (X : ℝ) (TripleCoefficientFibre.triples P Q S) (TripleCoefficientFibre.coefficient f X) TripleCoefficientFibre.level)‖ := by congr 1; abel
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add le_rfl he)
  have hr := htri.trans (add_le_add hb le_rfl)
  simpa only [TripleCoefficientFibre.polynomial_factorization f X P Q S (fun p hp ↦ (hP p hp).1) hQ hS,
    norm_mul,EulerIntegralLimit.weight,div_mul_eq_mul_div,mul_assoc] using hr


theorem full_series_bound_eventually :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ f : ℕ →* ℂ,
      (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) → ∀ (U : ℝ) (P : Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ 2*p ≤ X ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*U) →
      ‖RealTripleConvolution.triple f X P‖ ≤ ((X : ℝ)/(2*Real.pi))*(∫ t : ℝ,
        EulerIntegralLimit.weight ((LogarithmicGaussianSum.width X)^2)
          P (PrimeFactorCauchy.bandCoefficient f (X : ℝ)) (TripleSharpIdentity.bandPrimes X U) f t*
          ‖FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) f t‖)+error X := by
  obtain ⟨X₀,hX₀,hh⟩ := finite_bound_eventually
  refine ⟨X₀,hX₀,?_⟩
  intro X hX f hf U P hP
  have hX2 := hX₀.trans hX
  have hδ := LogarithmicGaussianSum.width_positive X hX2
  have hE : ∀ p ∈ FixedEulerTruncation.primes X, p.Prime := FixedEulerTruncation.primes_prime X
  have hfE : ∀ n ∈ Nat.factoredNumbers (FixedEulerTruncation.primes X), ‖f n‖ ≤ 1 := by
    intro n hn
    exact hf n (Nat.pos_of_ne_zero hn.1)
  have hlim := EulerIntegralLimit.integral_truncation_tendsto ((LogarithmicGaussianSum.width X)^2)
    (sq_pos_of_pos hδ) P (PrimeFactorCauchy.bandCoefficient f (X : ℝ))
    (TripleSharpIdentity.bandPrimes X U) f (FixedEulerTruncation.primes X) hE f hfE
  apply ge_of_tendsto ((hlim.const_mul ((X : ℝ)/(2*Real.pi))).add_const (error X))
  filter_upwards [eventually_ge_atTop X] with Y hY
  have hS := FixedEulerTruncation.support_positive (FixedEulerTruncation.primes X) Y
  have hcover := FixedEulerTruncation.support_contains X Y hY
  have hfinite := hh X hX f hf P (TripleSharpIdentity.bandPrimes X U)
    (FixedEulerTruncation.support (FixedEulerTruncation.primes X) Y)
    (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.1⟩) (TripleSharpIdentity.band_primes_prime X U) hS
  rw [TripleSharpIdentity.band_sharp_eq_triple f X U P _ (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.2⟩) hS hcover] at hfinite
  exact hfinite

theorem real_full_euler_bound_eventually :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ f : ℕ →* ℝ,
      (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ (U : ℝ) (P : Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ 2*p ≤ X ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*U) →
      ‖RealTripleConvolution.triple (FullTriplePerron.complexify f) X P‖ ≤ ((X : ℝ)/(2*Real.pi))*(∫ t : ℝ,
        EulerIntegralLimit.weight ((LogarithmicGaussianSum.width X)^2)
          P (PrimeFactorCauchy.bandCoefficient (FullTriplePerron.complexify f) (X : ℝ))
          (TripleSharpIdentity.bandPrimes X U) (FullTriplePerron.complexify f) t*
          ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖)+error X := by
  obtain ⟨X₀,hX₀,hh⟩ := full_series_bound_eventually
  refine ⟨X₀,hX₀,?_⟩
  intro X hX f hf U P hP
  have hr := hh X hX (FullTriplePerron.complexify f) (FullTriplePerron.complexify_bound f hf) U P hP
  simpa only [FullTriplePerron.real_series_eq_product (FixedEulerTruncation.primes X)
    (FixedEulerTruncation.primes_prime X) f hf] using hr
end PaperP1.QuantitativeTriplePerron
