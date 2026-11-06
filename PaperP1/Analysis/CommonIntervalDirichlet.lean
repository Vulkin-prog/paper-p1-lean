module

public import PaperP1.Analysis.DirichletPolynomialMeanValue
public import PaperP1.Analysis.CommonPresenceWeightedSum
public import PaperP1.Analysis.CommonUniformWeightedSum
public import PaperP1.Analysis.DyadicPartialSummation

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CommonIntervalDirichlet
open Finset Nat MeasureTheory PaperP1 LogarithmicPhase
open scoped Classical

def coefficient (P Q : Finset ℕ) (f : ℕ →* ℝ) (n : ℕ) : ℂ :=
  (f n : ℂ)*(PrimePresence.present Q n : ℂ)/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ)

theorem value_as_twisted_sum (S : Finset ℕ) (c : ℕ → ℂ) (τ : ℝ) :
    DirichletPolynomialMeanValue.value S c τ=
      ∑ n ∈ S, (c n*phase (-Real.log (n : ℝ)) τ)/(n : ℂ) := by
  unfold DirichletPolynomialMeanValue.value GaussianExponentialSums.polynomial
  apply sum_congr rfl
  intro n hn
  ring

theorem common_interval_small (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∃ N₀ : ℕ, 5 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ T : ℝ, 1 ≤ T →
      (ActualEulerBand.frequencyCutoff (2*N) : ℝ) ≤ T →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioc (-T) T ∧ volume.real E ≤ δ*T ∧
        ∀ M : ℕ, N ≤ M → M ≤ 2*N → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ R < (p : ℝ)) →
          ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) → ∀ f : ℕ →* ℝ,
          (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ τ ∈ Set.Ioc (-T) T, τ ∉ E →
          ‖DirichletPolynomialMeanValue.value (Ico N M) (coefficient P Q f) τ‖ ≤ ε := by
  obtain ⟨R,hR,N₁,hN₁,hs⟩ := CommonUniformWeightedSum.common_uniform_presence_small (ε/4) δ (by positivity) hδ
  refine ⟨R,hR,N₁+1,by omega,?_⟩
  intro N hN T hT hcut
  obtain ⟨E,hE,hsub,hm,hoff⟩ := hs (N-1) (by omega) (2*N) (by omega) T hT hcut
  refine ⟨E,hE,hsub,hm,?_⟩
  intro M hNM hMN P hP Q hQ f hf τ hτ hnot
  let a := fun n : ℕ ↦ coefficient P Q f n*phase (-Real.log (n : ℝ)) τ
  have hpartial : ∀ X : ℕ, N-1 ≤ X → X ≤ 2*N → ‖∑ n ∈ Icc 1 X, a n‖ ≤ (ε/4)*(X : ℝ) := by
    intro X hLX hUX
    change ‖CommonPresenceWeightedSum.weighted X P Q f τ‖ ≤ _
    exact hoff X hLX hUX P hP Q hQ f hf τ hτ hnot
  have hh := DyadicPartialSummation.weighted_interval_bound N M (by omega) hNM hMN a (ε/4) (by positivity) hpartial
  rw [value_as_twisted_sum]
  change ‖∑ n ∈ Ico N M, a n/(n : ℂ)‖ ≤ ε
  exact hh.trans_eq (by ring)
end PaperP1.CommonIntervalDirichlet
