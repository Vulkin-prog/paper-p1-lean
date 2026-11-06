module

public import PaperP1.Analysis.CommonDampedSum
public import PaperP1.Analysis.CountWeightedSum
public import PaperP1.Analysis.UniformRealTwistedSum

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UniformCountWeightedTwistedSum
open Finset Filter MeasureTheory PaperP1 LogarithmicPhase
open scoped Classical

theorem multiplicity_uniform_bound (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ P : Finset ℕ,
      ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      ∀ τ : ℝ, T₀ ≤ |τ| → |τ| ≤ (X : ℝ)^B →
      ‖∑ n ∈ Icc 1 X, ((f n : ℂ)/((ValuationDamping.multiplicity P n+1 : ℕ) : ℂ))*
        phase (-Real.log (n : ℝ)) τ‖ ≤ ε*(X : ℝ) := by
  obtain ⟨T₀,hT₀,X₀,hX₀,hBound⟩ := UniformRealTwistedSum.uniform_bound B ε hB hε
  refine ⟨T₀,hT₀,X₀,hX₀,?_⟩
  intro X hX P f hf τ hLower hUpper
  rw [← CommonDampedSum.twisted_sum_integral X P f τ]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := ε*(X : ℝ)) (fun z hz ↦ by
    have hz' : z ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hz
    have hzUnit : |z| ≤ 1 := by rw [abs_of_nonneg hz'.1.le]; exact hz'.2
    exact hBound X hX (ValuationDamping.damped P f z)
      (ValuationDamping.damped_prime_bound P f hf z hzUnit) τ hLower hUpper)
  simpa using hh

theorem count_uniform_bound (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ R : ℝ, 2 ≤ R ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ X ≥ X₀,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ R < (p : ℝ)) →
      ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      ∀ τ : ℝ, T₀ ≤ |τ| → |τ| ≤ (X : ℝ)^B →
      ‖∑ n ∈ Icc 1 X, ((f n : ℂ)/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ))*
        phase (-Real.log (n : ℝ)) τ‖ ≤ ε*(X : ℝ) := by
  obtain ⟨T₀,hT₀,X₀,hX₀,hBound⟩ := multiplicity_uniform_bound B (ε/2) hB (by positivity)
  let R : ℝ := max 2 (8/ε)
  have hR : 2 ≤ R := le_max_left _ _
  have hRP : 0 < R := by linarith only [hR]
  have hError : 4/R ≤ ε/2 := by
    apply (div_le_iff₀ hRP).mpr
    have hh := (div_le_iff₀ hε).mp (le_max_right 2 (8/ε))
    nlinarith only [hh]
  refine ⟨R,hR,T₀,hT₀,X₀,hX₀,?_⟩
  intro X hX P hP f hf τ hLower hUpper
  have hMultiplicity := hBound X hX P f hf τ hLower hUpper
  have hDifference := CountWeightedSum.actual_difference_bound X P (fun p hp ↦ (hP p hp).1) f hf τ
  have hSquares := CountWeightedSum.square_count_bound P X R hR (fun p hp ↦ (hP p hp).2)
  let A := ∑ n ∈ Icc 1 X, ((f n : ℂ)/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ
  let C := ∑ n ∈ Icc 1 X, ((f n : ℂ)/((ValuationDamping.multiplicity P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ
  have hTriangle : ‖A‖ ≤ ‖A-C‖+‖C‖ := by
    simpa only [sub_add_cancel] using norm_add_le (A-C) C
  dsimp only [A,C] at hTriangle
  have hScale := mul_le_mul_of_nonneg_right hError (Nat.cast_nonneg X : (0 : ℝ) ≤ X)
  have hException : 2*((PrimeDivisorWeights.squareExceptions P X).card : ℝ) ≤ (ε/2)*(X : ℝ) := by
    calc
      _ ≤ 2*(2*(X : ℝ)/R) := mul_le_mul_of_nonneg_left hSquares (by norm_num)
      _ = (4/R)*(X : ℝ) := by ring
      _ ≤ _ := hScale
  linarith only [hTriangle,hDifference,hMultiplicity,hException]
end PaperP1.UniformCountWeightedTwistedSum
