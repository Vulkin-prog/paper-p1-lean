module

public import PaperP1.Analysis.GaussianFibreError
public import PaperP1.Analysis.TripleSharpIdentity
public import PaperP1.Analysis.EulerIntegralLimit
set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FullTriplePerron
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

theorem actual_full_series_perron (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ (f : ℕ →* ℂ),
      (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) → ∀ (U : ℝ) (P : Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ 2*p ≤ X ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*U) →
      ‖RealTripleConvolution.triple f X P‖ ≤ ((X : ℝ)/(2*Real.pi))*(∫ t : ℝ,
        EulerIntegralLimit.weight ((LogarithmicGaussianSum.width X)^2)
          P (PrimeFactorCauchy.bandCoefficient f (X : ℝ)) (TripleSharpIdentity.bandPrimes X U) f t*
          ‖FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) f t‖)+ε*(X : ℝ) := by
  obtain ⟨X₀,hX₀,hh⟩ := GaussianFibreError.actual_finite_triple_perron ε hε
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
  apply ge_of_tendsto ((hlim.const_mul ((X : ℝ)/(2*Real.pi))).add_const (ε*(X : ℝ)))
  filter_upwards [eventually_ge_atTop X] with Y hY
  have hS := FixedEulerTruncation.support_positive (FixedEulerTruncation.primes X) Y
  have hcover := FixedEulerTruncation.support_contains X Y hY
  have hfinite := hh X hX f hf P (TripleSharpIdentity.bandPrimes X U)
    (FixedEulerTruncation.support (FixedEulerTruncation.primes X) Y)
    (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.1⟩) (TripleSharpIdentity.band_primes_prime X U) hS
  rw [TripleSharpIdentity.band_sharp_eq_triple f X U P _ (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.2⟩) hS hcover] at hfinite
  simpa only [EulerIntegralLimit.weight,div_mul_eq_mul_div] using hfinite

def complexify (f : ℕ →* ℝ) : ℕ →* ℂ where
  toFun n := (f n : ℂ)
  map_one' := by simp
  map_mul' m n := by simp only [f.map_mul,Complex.ofReal_mul]

theorem complexify_bound (f : ℕ →* ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1)
    (n : ℕ) (hn : 0 < n) : ‖complexify f n‖ ≤ 1 := by
  rw [show complexify f n=(f n : ℂ) from rfl,Complex.norm_real,Real.norm_eq_abs]
  exact FinitePrimeDirichletTruncation.real_hom_bound f hf n hn.ne'

theorem real_series_eq_product (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    (f : ℕ →* ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (t : ℝ) :
    FinitePrimeDirichletTruncation.total E (complexify f) t=RealPrimeEulerBound.product E f t := by
  exact FinitePrimeDirichletSeries.value_eq_product E hE f hf t

theorem real_euler_integrable (b : ℝ) (hb : 0 < b) (P : Finset ℕ) (a : ℕ → ℂ)
    (Q E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) (f : ℕ →* ℝ)
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) :
    Integrable (fun t : ℝ ↦ EulerIntegralLimit.weight b P a Q (complexify f) t*‖RealPrimeEulerBound.product E f t‖) := by
  have hfE : ∀ n ∈ Nat.factoredNumbers E, ‖complexify f n‖ ≤ 1 := by
    intro n hn
    exact complexify_bound f hf n (Nat.pos_of_ne_zero hn.1)
  have hh := EulerIntegralLimit.total_integrable b hb P a Q (complexify f) E hE (complexify f) hfE
  simpa only [real_series_eq_product E hE f hf] using hh

theorem real_full_euler_perron (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ (f : ℕ →* ℝ),
      (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ (U : ℝ) (P : Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ 2*p ≤ X ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*U) →
      ‖RealTripleConvolution.triple (complexify f) X P‖ ≤ ((X : ℝ)/(2*Real.pi))*(∫ t : ℝ,
        EulerIntegralLimit.weight ((LogarithmicGaussianSum.width X)^2)
          P (PrimeFactorCauchy.bandCoefficient (complexify f) (X : ℝ))
          (TripleSharpIdentity.bandPrimes X U) (complexify f) t*
          ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖)+ε*(X : ℝ) := by
  obtain ⟨X₀,hX₀,hh⟩ := actual_full_series_perron ε hε
  refine ⟨X₀,hX₀,?_⟩
  intro X hX f hf U P hP
  have hr := hh X hX (complexify f) (complexify_bound f hf) U P hP
  simpa only [real_series_eq_product (FixedEulerTruncation.primes X) (FixedEulerTruncation.primes_prime X) f hf] using hr
end PaperP1.FullTriplePerron
