module

public import PaperP1.Analysis.PrimeFactorCauchy
public import PaperP1.Arithmetic.PrimeTruncation
public import PaperP1.Analysis.ActualEulerBand
public import PaperP1.Analysis.ComplexEuler
public import PaperP1.Analysis.ComplexEulerFrequencyTruncation
public import PaperP1.Analysis.EulerFrequencyTruncation
public import PaperP1.Analysis.LogarithmicGaussianTail
public import PaperP1.Analysis.QuantitativeTriplePerron
public import PaperP1.Analysis.WeightedPerronError

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.QuantitativeEulerBand
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

theorem band_integral_bound (X : ℕ) (hX : 2 ≤ X) (hlog : 1 ≤ Real.log (X : ℝ))
    (g : ℕ →* ℂ) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (U : ℝ) (hU : Real.log 2 ≤ U)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ (LogarithmicGaussianTail.height X)^2 ≤ (p : ℝ) ∧
      U ≤ Real.log ((X : ℝ)/(p : ℝ)) ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*U) :
    (∫ t in -(LogarithmicGaussianTail.height X)..LogarithmicGaussianTail.height X,
      ComplexEulerFrequencyTruncation.base X g P (TripleSharpIdentity.bandPrimes X U) t) ≤
      PrimeFactorCauchy.bandConstant*Real.sqrt (PrimeUnitMean.frequencyBudget
        (FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) g) (ActualEulerBand.frequencyCutoff X)) := by
  have hT : 1 ≤ LogarithmicGaussianTail.height X := by
    simpa only [LogarithmicGaussianTail.height,one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlog 10
  have hF := ComplexEuler.total_continuous (FixedEulerTruncation.primes X) (FixedEulerTruncation.primes_prime X) g hg
  exact PrimeFactorCauchy.band_factor_integral_bound P (TripleSharpIdentity.bandPrimes X U) g g _ hF (X : ℝ) U
    (by exact_mod_cast (by omega : 0 < X)) hU (ActualEulerBand.frequencyCutoff X) (LogarithmicGaussianTail.height X)
    hT (ActualEulerBand.frequency_cover X) (fun p hp ↦ hg p (hP p hp).1)
    (fun q hq ↦ hg q (TripleSharpIdentity.band_primes_prime X U q hq)) hP
    (fun q hq ↦ ⟨TripleSharpIdentity.band_primes_prime X U q hq,TripleSharpIdentity.band_primes_log X U q hq⟩)

theorem quantitative_band_bound :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ g : ℕ →* ℂ, (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ U : ℝ, Real.log 2 ≤ U → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ 2*p ≤ X ∧ (LogarithmicGaussianTail.height X)^2 ≤ (p : ℝ) ∧
        U ≤ Real.log ((X : ℝ)/(p : ℝ)) ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*U) →
      ‖RealTripleConvolution.triple g X P‖ ≤
        ActualEulerBand.constant*(X : ℝ)*Real.sqrt (PrimeUnitMean.frequencyBudget
          (FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) g) (ActualEulerBand.frequencyCutoff X))+
            WeightedPerronError.combinedError X := by
  obtain ⟨X₁,hX₁,hperron⟩ := QuantitativeTriplePerron.full_series_bound_eventually
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨X₂,hX₂⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop 1))
  refine ⟨max X₁ (max X₂ 2),by omega,?_⟩
  intro X hX g hg U hU P hP
  have hX2 : 2 ≤ X := by omega
  have hA : 0 ≤ (X : ℝ)/(2*Real.pi) := by positivity
  have hp := hperron X (by omega) g (fun n hn ↦ ComplexEuler.complex_hom_bound g hg n hn.ne') U P
    (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.1,(hP p hp).2.2.2.2⟩)
  have ht := ComplexEulerFrequencyTruncation.whole_integral_bound X hX2 g hg P (TripleSharpIdentity.bandPrimes X U)
    (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.1⟩)
    (fun q hq ↦ ⟨TripleSharpIdentity.band_primes_prime X U q hq,ActualEulerBand.band_primes_le X U q hq⟩)
  have hb := band_integral_bound X hX2 (hX₂ X (by omega)) g hg U hU P
    (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.2⟩)
  have hfirst := hp.trans (add_le_add (mul_le_mul_of_nonneg_left ht hA) le_rfl)
  have hsecond := hfirst.trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hb le_rfl) hA) le_rfl)
  calc
    _ ≤ ((X : ℝ)/(2*Real.pi))*(PrimeFactorCauchy.bandConstant*Real.sqrt (PrimeUnitMean.frequencyBudget
          (FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) g) (ActualEulerBand.frequencyCutoff X))+
          EulerFrequencyTruncation.scaledTail X)+QuantitativeTriplePerron.error X := hsecond
    _ = _ := by dsimp only [ActualEulerBand.constant,WeightedPerronError.combinedError]; ring

theorem height_sq_le_of_cutoff (X p : ℕ) (hp : PrimeTruncation.cutoff 20 X < p) :
    (LogarithmicGaussianTail.height X)^2 ≤ (p : ℝ) := by
  have hh := Nat.lt_floor_add_one ((Real.log (X : ℝ))^20)
  have hpN : ⌊(Real.log (X : ℝ))^20⌋₊+1 ≤ p := by change ⌊(Real.log (X : ℝ))^20⌋₊ < p at hp; omega
  have hpR : (⌊(Real.log (X : ℝ))^20⌋₊ : ℝ)+1 ≤ (p : ℝ) := by exact_mod_cast hpN
  have he : (LogarithmicGaussianTail.height X)^2=(Real.log (X : ℝ))^20 := by dsimp only [LogarithmicGaussianTail.height]; ring
  rw [he]
  exact hh.le.trans hpR

theorem retained_band_bound :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ g : ℕ →* ℂ, (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ U : ℝ, Real.log 2 ≤ U → ∀ P : Finset ℕ,
      (P ⊆ PrimeTruncation.retained X (PrimeTruncation.cutoff 20 X)) →
      (∀ p ∈ P, U ≤ Real.log ((X : ℝ)/(p : ℝ)) ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*U) →
      ‖RealTripleConvolution.triple g X P‖ ≤
        ActualEulerBand.constant*(X : ℝ)*Real.sqrt (PrimeUnitMean.frequencyBudget
          (FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) g) (ActualEulerBand.frequencyCutoff X))+
            WeightedPerronError.combinedError X := by
  obtain ⟨X₀,hX₀,hh⟩ := quantitative_band_bound
  refine ⟨X₀,hX₀,?_⟩
  intro X hX g hg U hU P hsub hband
  apply hh X hX g hg U hU P
  intro p hp
  have hmem := (mem_filter.mp (hsub hp)).2
  exact ⟨hmem.1,hmem.2.2,height_sq_le_of_cutoff X p hmem.2.1,hband p hp⟩
end PaperP1.QuantitativeEulerBand
