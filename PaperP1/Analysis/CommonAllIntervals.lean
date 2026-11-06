module

public import PaperP1.Analysis.CommonIntervalDirichlet
public import PaperP1.Analysis.CommonUniformWeightedSum
public import PaperP1.Analysis.DyadicPartialSummation

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CommonAllIntervals
open Finset PaperP1 MeasureTheory LogarithmicPhase
open scoped Classical

theorem common_all_intervals_small (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ B : ℕ, N ≤ B →
      ∀ T : ℝ, 1 ≤ T → (ActualEulerBand.frequencyCutoff B : ℝ) ≤ T →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioc (-T) T ∧ volume.real E ≤ δ*T ∧
        ∀ L M : ℕ, N < L → L ≤ M → M ≤ 2*L → 2*L ≤ B →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ R < (p : ℝ)) →
          ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) → ∀ f : ℕ →* ℝ,
          (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ τ ∈ Set.Ioc (-T) T, τ ∉ E →
          ‖DirichletPolynomialMeanValue.value (Ico L M) (CommonIntervalDirichlet.coefficient P Q f) τ‖ ≤ ε := by
  obtain ⟨R,hR,N₀,hN₀,hs⟩ := CommonUniformWeightedSum.common_uniform_presence_small (ε/4) δ (by positivity) hδ
  refine ⟨R,hR,N₀,hN₀,?_⟩
  intro N hN B hNB T hT hcut
  obtain ⟨E,hE,hsub,hm,hoff⟩ := hs N hN B hNB T hT hcut
  refine ⟨E,hE,hsub,hm,?_⟩
  intro L M hNL hLM hML hLB P hP Q hQ f hf τ hτ hnot
  let a := fun n : ℕ ↦ CommonIntervalDirichlet.coefficient P Q f n*phase (-Real.log (n : ℝ)) τ
  have hpartial : ∀ X : ℕ, L-1 ≤ X → X ≤ 2*L → ‖∑ n ∈ Icc 1 X, a n‖ ≤ (ε/4)*(X : ℝ) := by
    intro X hLX hXL
    change ‖CommonPresenceWeightedSum.weighted X P Q f τ‖ ≤ _
    exact hoff X (by omega) (by omega) P hP Q hQ f hf τ hτ hnot
  have hh := DyadicPartialSummation.weighted_interval_bound L M (by omega) hLM hML a (ε/4) (by positivity) hpartial
  rw [CommonIntervalDirichlet.value_as_twisted_sum]
  change ‖∑ n ∈ Ico L M, a n/(n : ℂ)‖ ≤ ε
  exact hh.trans_eq (by ring)
end PaperP1.CommonAllIntervals
