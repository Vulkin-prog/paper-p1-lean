module

public import PaperP1.Analysis.FullTriplePerron
public import PaperP1.Analysis.PrimeFactorCauchy
public import PaperP1.Analysis.EulerFrequencyTruncation
public import PaperP1.Analysis.LogarithmicGaussianTail

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ActualEulerBand
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

def frequencyCutoff (X : ℕ) : ℕ := ⌈LogarithmicGaussianTail.height X⌉₊

def constant : ℝ := PrimeFactorCauchy.bandConstant/(2*Real.pi)

theorem constant_pos : 0 < constant := by
  have hc := PrimeFactorCauchy.bandConstant_pos
  dsimp only [constant]
  positivity

theorem frequency_cover (X : ℕ) : LogarithmicGaussianTail.height X ≤ (frequencyCutoff X : ℝ)+1/2 := by
  have hh : LogarithmicGaussianTail.height X ≤ (frequencyCutoff X : ℝ) := Nat.le_ceil _
  linarith

theorem band_primes_le (X : ℕ) (U : ℝ) (q : ℕ) (hq : q ∈ TripleSharpIdentity.bandPrimes X U) : q ≤ X :=
  (mem_Icc.mp (mem_filter.mp (mem_filter.mp hq).1).1).2

theorem band_integral_bound (X : ℕ) (hX : 2 ≤ X) (hlog : 1 ≤ Real.log (X : ℝ))
    (f : ℕ → ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (U : ℝ) (hU : Real.log 2 ≤ U)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ (LogarithmicGaussianTail.height X)^2 ≤ (p : ℝ) ∧
      U ≤ Real.log ((X : ℝ)/(p : ℝ)) ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*U) :
    (∫ t in -(LogarithmicGaussianTail.height X)..LogarithmicGaussianTail.height X,
      EulerFrequencyTruncation.base X f P (TripleSharpIdentity.bandPrimes X U) t) ≤
      PrimeFactorCauchy.bandConstant*Real.sqrt (PrimeUnitMean.frequencyBudget
        (RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f) (frequencyCutoff X)) := by
  have hT : 1 ≤ LogarithmicGaussianTail.height X := by
    simpa only [LogarithmicGaussianTail.height,one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlog 10
  have hF := RealPrimeEulerBound.product_continuous (FixedEulerTruncation.primes X) (FixedEulerTruncation.primes_prime X)
    f (fun p hp ↦ hf p (FixedEulerTruncation.primes_prime X p hp))
  have hh := PrimeFactorCauchy.band_factor_integral_bound P (TripleSharpIdentity.bandPrimes X U)
    (fun n ↦ (f n : ℂ)) (fun n ↦ (f n : ℂ)) _ hF (X : ℝ) U
    (by exact_mod_cast (by omega : 0 < X)) hU (frequencyCutoff X) (LogarithmicGaussianTail.height X)
    hT (frequency_cover X) (by
      intro p hp
      simpa only [Complex.norm_real,Real.norm_eq_abs] using hf p (hP p hp).1) (by
      intro q hq
      simpa only [Complex.norm_real,Real.norm_eq_abs] using hf q (TripleSharpIdentity.band_primes_prime X U q hq)) hP
    (fun q hq ↦ ⟨TripleSharpIdentity.band_primes_prime X U q hq,TripleSharpIdentity.band_primes_log X U q hq⟩)
  exact hh


theorem real_band_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      ∀ U : ℝ, Real.log 2 ≤ U → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ 2*p ≤ X ∧ (LogarithmicGaussianTail.height X)^2 ≤ (p : ℝ) ∧
        U ≤ Real.log ((X : ℝ)/(p : ℝ)) ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*U) →
      ‖RealTripleConvolution.triple (FullTriplePerron.complexify f) X P‖ ≤
        constant*(X : ℝ)*Real.sqrt (PrimeUnitMean.frequencyBudget
          (RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f) (frequencyCutoff X))+ε*(X : ℝ) := by
  obtain ⟨X₁,hX₁,hperron⟩ := FullTriplePerron.real_full_euler_perron (ε/2) (by positivity)
  obtain ⟨X₂,hX₂,htrunc⟩ := EulerFrequencyTruncation.whole_integral_small_uniform (Real.pi*ε) (by positivity)
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨X₃,hX₃⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop 1))
  refine ⟨max (max X₁ X₂) (max X₃ 2),by omega,?_⟩
  intro X hX f hf U hU P hP
  have hX2 : 2 ≤ X := by omega
  have hA : 0 ≤ (X : ℝ)/(2*Real.pi) := by positivity
  have hp := hperron X (by omega) f hf U P (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.1,(hP p hp).2.2.2.2⟩)
  have ht := htrunc X (by omega) f hf P (TripleSharpIdentity.bandPrimes X U)
    (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.1⟩)
    (fun q hq ↦ ⟨TripleSharpIdentity.band_primes_prime X U q hq,band_primes_le X U q hq⟩)
  have hb := band_integral_bound X hX2 (hX₃ X (by omega)) f hf U hU P
    (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.2⟩)
  have hfirst := hp.trans (add_le_add (mul_le_mul_of_nonneg_left ht hA) le_rfl)
  have hsecond := hfirst.trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hb le_rfl) hA) le_rfl)
  calc
    _ ≤ ((X : ℝ)/(2*Real.pi))*(PrimeFactorCauchy.bandConstant*Real.sqrt (PrimeUnitMean.frequencyBudget
          (RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f) (frequencyCutoff X))+Real.pi*ε)+(ε/2)*(X : ℝ) := hsecond
    _ = _ := by dsimp only [constant]; field_simp [Real.pi_ne_zero]; ring
end PaperP1.ActualEulerBand
