module

public import PaperP1.Analysis.CommonRealTwistedSum
public import PaperP1.Analysis.DampedDirichletIntegral
public import PaperP1.Analysis.ValuationDamping

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CommonDampedSum
open Finset Nat MeasureTheory PaperP1 LogarithmicPhase
open scoped Classical

theorem twisted_sum_integral (X : ℕ) (P : Finset ℕ) (f : ℕ →* ℝ) (τ : ℝ) :
    (∫ z in (0 : ℝ)..1, ∑ n ∈ Icc 1 X,
      (ValuationDamping.damped P f z n : ℂ)*phase (-Real.log (n : ℝ)) τ)=
    ∑ n ∈ Icc 1 X,
      ((f n : ℂ)/((ValuationDamping.multiplicity P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ := by
  exact DampedDirichletIntegral.weighted_sum_integral (Icc 1 X) P
    (fun n hn ↦ by have hh := (mem_Icc.mp hn).1; omega) f (fun n ↦ phase (-Real.log (n : ℝ)) τ)

theorem common_weighted_summatory_small (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ T : ℝ, 1 ≤ T →
      (ActualEulerBand.frequencyCutoff X : ℝ) ≤ T →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioc (-T) T ∧ volume.real E ≤ δ*T ∧
        ∀ P : Finset ℕ, ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
          ∀ τ ∈ Set.Ioc (-T) T, τ ∉ E →
          ‖∑ n ∈ Icc 1 X,
            ((f n : ℂ)/((ValuationDamping.multiplicity P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ‖ ≤ ε*(X : ℝ) := by
  obtain ⟨X₀,hX₀,hs⟩ := CommonRealTwistedSum.common_twisted_summatory_small ε δ hε hδ
  refine ⟨X₀,hX₀,?_⟩
  intro X hX T hT hcut
  obtain ⟨E,hE,hsub,hm,hoff⟩ := hs X hX T hT hcut
  refine ⟨E,hE,hsub,hm,?_⟩
  intro P f hf τ hτ hnot
  rw [← twisted_sum_integral X P f τ]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := ε*(X : ℝ)) (fun z hz ↦ by
    have hz' : z ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hz
    have hzunit : |z| ≤ 1 := by rw [abs_of_nonneg hz'.1.le]; exact hz'.2
    exact hoff (ValuationDamping.damped P f z)
      (ValuationDamping.damped_prime_bound P f hf z hzunit) τ hτ hnot)
  simpa using hh
end PaperP1.CommonDampedSum
