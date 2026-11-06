module

public import PaperP1.Analysis.FullTriplePerron
public import PaperP1.Analysis.PrimeUnitMean
public import PaperP1.Analysis.ActualEulerBand
public import PaperP1.Analysis.QuantitativeEulerBand
public import PaperP1.Analysis.WeightedPerronError

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.RealUnitTwist
open Finset Nat MeasureTheory PaperP1 LogarithmicPhase Filter
open scoped Classical

def unitTwist (f : ℕ →* ℝ) (τ : ℝ) : ℕ →* ℂ :=
  (Nat.castRingHom ℂ).toMonoidHom*FinitePrimeDirichletSeries.twistHom f τ

theorem unitTwist_apply (f : ℕ →* ℝ) (τ : ℝ) (n : ℕ) (hn : n ≠ 0) :
    unitTwist f τ n=(f n : ℂ)*phase (-Real.log (n : ℝ)) τ := by
  change (n : ℂ)*((f n : ℂ)/(n : ℂ)*phase (-Real.log (n : ℝ)) τ)=_
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  field_simp [hnC]

theorem unitTwist_zero (f : ℕ →* ℝ) (τ : ℝ) : unitTwist f τ 0=0 := by
  simp [unitTwist]

theorem unitTwist_norm (f : ℕ →* ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1)
    (τ : ℝ) (n : ℕ) (hn : n ≠ 0) : ‖unitTwist f τ n‖ ≤ 1 := by
  rw [unitTwist_apply f τ n hn,norm_mul,phase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact FinitePrimeDirichletTruncation.real_hom_bound f hf n hn

theorem unitTwist_prime_bound (f : ℕ →* ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (τ : ℝ) :
    ∀ p : ℕ, p.Prime → ‖unitTwist f τ p‖ ≤ 1 := fun p hp ↦ unitTwist_norm f hf τ p hp.ne_zero

theorem twist_identity (f : ℕ →* ℝ) (τ t : ℝ) (n : ℕ) :
    DirichletRamareApproximation.twist (unitTwist f τ) n t=
      DirichletRamareApproximation.twist (fun n ↦ (f n : ℂ)) n (t+τ) := by
  by_cases hn : n=0
  · subst n
    simp only [DirichletRamareApproximation.twist,unitTwist_zero,Nat.cast_zero,div_zero,zero_mul]
  · rw [DirichletRamareApproximation.twist,unitTwist_apply f τ n hn,DirichletRamareApproximation.twist,
      PrimeUnitMean.phase_time_add]
    ring

theorem total_twist_eq_series (P : Finset ℕ) (f : ℕ →* ℝ) (τ t : ℝ) :
    FinitePrimeDirichletTruncation.total P (unitTwist f τ) t=FinitePrimeDirichletSeries.value P f (t+τ) := by
  apply tsum_congr
  intro n
  exact twist_identity f τ t n

theorem total_twist_eq_euler (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ →* ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (τ t : ℝ) :
    FinitePrimeDirichletTruncation.total P (unitTwist f τ) t=RealPrimeEulerBound.product P f (t+τ) := by
  rw [total_twist_eq_series,FinitePrimeDirichletSeries.value_eq_product P hP f hf]

theorem frequencyBudget_twist_eq (X : ℕ) (f : ℕ →* ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (τ : ℝ) (K : ℕ) :
    PrimeUnitMean.frequencyBudget (FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) (unitTwist f τ)) K=
      PrimeUnitMean.frequencyBudget (fun t ↦ RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (t+τ)) K := by
  have he : FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) (unitTwist f τ)=
      fun t ↦ RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (t+τ) :=
    funext (total_twist_eq_euler _ (FixedEulerTruncation.primes_prime X) f hf τ)
  rw [he]

theorem summatory_twist (X : ℕ) (f : ℕ →* ℝ) (τ : ℝ) :
    MultiplicativeLogConvolution.summatory (unitTwist f τ) X=
      ∑ n ∈ Icc 1 X, (f n : ℂ)*phase (-Real.log (n : ℝ)) τ := by
  apply sum_congr rfl
  intro n hn
  exact unitTwist_apply f τ n (by have hh := (mem_Icc.mp hn).1; omega)


theorem twisted_retained_band_bound :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ τ : ℝ,
      ∀ U : ℝ, Real.log 2 ≤ U → ∀ P : Finset ℕ,
      (P ⊆ PrimeTruncation.retained X (PrimeTruncation.cutoff 20 X)) →
      (∀ p ∈ P, U ≤ Real.log ((X : ℝ)/(p : ℝ)) ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*U) →
      ‖RealTripleConvolution.triple (unitTwist f τ) X P‖ ≤
        ActualEulerBand.constant*(X : ℝ)*Real.sqrt (PrimeUnitMean.frequencyBudget
          (fun t ↦ RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (t+τ)) (ActualEulerBand.frequencyCutoff X))+
            WeightedPerronError.combinedError X := by
  obtain ⟨X₀,hX₀,hh⟩ := QuantitativeEulerBand.retained_band_bound
  refine ⟨X₀,hX₀,?_⟩
  intro X hX f hf τ U hU P hsub hband
  have hb := hh X hX (unitTwist f τ) (unitTwist_prime_bound f hf τ) U hU P hsub hband
  simpa only [frequencyBudget_twist_eq X f hf τ] using hb
end PaperP1.RealUnitTwist
