module

public import PaperP1.Arithmetic.PrimeRangeSquareBudget
public import PaperP1.Analysis.PrimePolynomialMoments

/-! # Uniform high moments and actual large-value measures for reciprocal prime-band polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeRangeHighMoments
open Finset PaperP1 PaperP1.GaussianExponentialSums PaperP1.LogarithmicPhase
  PaperP1.DirichletPolynomialMeanValue PrimeRangeSquareBudget
open scoped Classical

theorem high_moment_bound (Y : ℕ) (hY : 1 < Y) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hband : ∀ p ∈ P, Y ≤ p ∧ p ≤ 2*Y)
    (hcard : (P.card : ℝ) ≤ 4*Y / Real.log Y)
    (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (k : ℕ) (T : ℝ) (hT : 0 < T) :
    (∫ t in -T..T, ‖value P a t‖^(2*k)) ≤
      Real.exp 1 * (Real.sqrt Real.pi*T + 2*Real.pi*(((2*Y)^k : ℕ) : ℝ)) *
        (k.factorial : ℝ) * (4/((Y : ℝ)*Real.log Y))^k := by
  have hm := PrimePolynomialMoments.high_moment_bound k (2*Y) (by omega) P hP
    (fun p hp ↦ (hband p hp).2) (fun p ↦ a p / (p : ℂ)) T hT
  have hs := reciprocal_square_budget Y hY P (fun p hp ↦ (hband p hp).1) hcard a ha
  have hp := pow_le_pow_left₀ (sum_nonneg (fun p hp ↦ sq_nonneg _)) hs k
  have hb := hm.trans (mul_le_mul_of_nonneg_left hp (by positivity))
  simpa only [value, polynomial] using hb

theorem large_values_measure (Y : ℕ) (hY : 1 < Y) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hband : ∀ p ∈ P, Y ≤ p ∧ p ≤ 2*Y)
    (hcard : (P.card : ℝ) ≤ 4*Y / Real.log Y)
    (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (k : ℕ) (T V : ℝ)
    (hT : 0 < T) (hV : 0 < V) :
    MeasureTheory.volume.real {t : ℝ | t ∈ Set.Ioc (-T) T ∧ V ≤ ‖value P a t‖} ≤
      (Real.exp 1 * (Real.sqrt Real.pi*T + 2*Real.pi*(((2*Y)^k : ℕ) : ℝ)) *
        (k.factorial : ℝ) * (4/((Y : ℝ)*Real.log Y))^k) / V^(2*k) := by
  have hm := PrimePolynomialMoments.large_values_measure k (2*Y) (by omega) P hP
    (fun p hp ↦ (hband p hp).2) (fun p ↦ a p / (p : ℂ)) T V hT hV
  have hs := reciprocal_square_budget Y hY P (fun p hp ↦ (hband p hp).1) hcard a ha
  have hp := pow_le_pow_left₀ (sum_nonneg (fun p hp ↦ sq_nonneg _)) hs k
  have hb := hm.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity)) (pow_nonneg hV.le _))
  simpa only [value, polynomial] using hb

theorem uniform_prime_range_estimates :
    ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Y ≤ p ∧ p ≤ 2*Y) →
      ∀ a : ℕ → ℂ, (∀ p ∈ P, ‖a p‖ ≤ 1) → ∀ k : ℕ, ∀ T : ℝ, 0 < T →
      ((∫ t in -T..T, ‖value P a t‖^(2*k)) ≤
        Real.exp 1 * (Real.sqrt Real.pi*T + 2*Real.pi*(((2*Y)^k : ℕ) : ℝ)) *
          (k.factorial : ℝ) * (4/((Y : ℝ)*Real.log Y))^k) ∧
      ∀ V : ℝ, 0 < V →
        MeasureTheory.volume.real {t : ℝ | t ∈ Set.Ioc (-T) T ∧ V ≤ ‖value P a t‖} ≤
          (Real.exp 1 * (Real.sqrt Real.pi*T + 2*Real.pi*(((2*Y)^k : ℕ) : ℝ)) *
            (k.factorial : ℝ) * (4/((Y : ℝ)*Real.log Y))^k) / V^(2*k) := by
  obtain ⟨Y₀,hY₀,hcount⟩ := prime_card_eventually
  refine ⟨Y₀,hY₀,?_⟩
  intro Y hY P hP hband a ha k T hT
  have hcard := hcount Y hY P hP (fun p hp ↦ (hband p hp).2)
  exact ⟨high_moment_bound Y (by omega) P hP hband hcard a ha k T hT,
    fun V hV ↦ large_values_measure Y (by omega) P hP hband hcard a ha k T V hT hV⟩
end PrimeRangeHighMoments
