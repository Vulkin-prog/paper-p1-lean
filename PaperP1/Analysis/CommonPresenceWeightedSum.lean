module

public import PaperP1.Analysis.CountWeightedSum
public import PaperP1.Analysis.PrimePresence

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CommonPresenceWeightedSum
open Finset Nat MeasureTheory PaperP1 LogarithmicPhase
open scoped Classical

def weighted (X : ℕ) (P Q : Finset ℕ) (f : ℕ →* ℝ) (τ : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 X, ((f n : ℂ)*(PrimePresence.present Q n : ℂ)/
    ((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ

theorem difference_identity (X : ℕ) (P Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (f : ℕ →* ℝ) (τ : ℝ) : weighted X P Q f τ=
      (∑ n ∈ Icc 1 X, ((f n : ℂ)/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ)-
      (∑ n ∈ Icc 1 X, ((ValuationDamping.damped Q f 0 n : ℂ)/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ) := by
  rw [← sum_sub_distrib]
  unfold weighted
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have hh := (mem_Icc.mp hn).1; omega
  have he := congrArg (fun x : ℝ ↦ (x : ℂ)) (PrimePresence.present_damped_difference Q hQ f n hn0)
  simp only [Complex.ofReal_mul,Complex.ofReal_sub] at he
  rw [he]
  ring

theorem common_presence_weighted_small (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ T : ℝ, 1 ≤ T →
      (ActualEulerBand.frequencyCutoff X : ℝ) ≤ T →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioc (-T) T ∧ volume.real E ≤ δ*T ∧
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ R < (p : ℝ)) →
          ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) →
          ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
          ∀ τ ∈ Set.Ioc (-T) T, τ ∉ E → ‖weighted X P Q f τ‖ ≤ ε*(X : ℝ) := by
  obtain ⟨R,hR,X₀,hX₀,hs⟩ := CountWeightedSum.common_count_weighted_small (ε/2) δ (by positivity) hδ
  refine ⟨R,hR,X₀,hX₀,?_⟩
  intro X hX T hT hcut
  obtain ⟨E,hE,hsub,hm,hoff⟩ := hs X hX T hT hcut
  refine ⟨E,hE,hsub,hm,?_⟩
  intro P hP Q hQ f hf τ hτ hnot
  have h1 := hoff P hP f hf τ hτ hnot
  have h2 := hoff P hP (ValuationDamping.damped Q f 0)
    (ValuationDamping.damped_prime_bound Q f hf 0 (by norm_num)) τ hτ hnot
  rw [difference_identity X P Q hQ f τ]
  exact (norm_sub_le _ _).trans (by linarith only [h1,h2])
end PaperP1.CommonPresenceWeightedSum
