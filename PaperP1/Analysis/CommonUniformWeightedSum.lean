module

public import PaperP1.Analysis.CommonPresenceWeightedSum
public import PaperP1.Analysis.CommonUniformTwistedSum

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CommonUniformWeightedSum
open Finset Nat MeasureTheory PaperP1 LogarithmicPhase
open scoped Classical

theorem common_uniform_presence_small (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ B : ℕ, N ≤ B →
      ∀ T : ℝ, 1 ≤ T → (ActualEulerBand.frequencyCutoff B : ℝ) ≤ T →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioc (-T) T ∧ volume.real E ≤ δ*T ∧
        ∀ X : ℕ, N ≤ X → X ≤ B → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ R < (p : ℝ)) →
          ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) → ∀ f : ℕ →* ℝ,
          (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ τ ∈ Set.Ioc (-T) T, τ ∉ E →
          ‖CommonPresenceWeightedSum.weighted X P Q f τ‖ ≤ ε*(X : ℝ) := by
  obtain ⟨N₀,hN₀,hs⟩ := CommonUniformTwistedSum.common_uniform_summatory_small (ε/4) δ (by positivity) hδ
  let R := max 2 (16/ε)
  have hR : 2 ≤ R := le_max_left _ _
  have hRp : 0 < R := by linarith
  have hsmall : 4/R ≤ ε/4 := by
    apply (div_le_iff₀ hRp).mpr
    have hh := (div_le_iff₀ hε).mp (le_max_right 2 (16/ε))
    nlinarith
  refine ⟨R,hR,N₀,hN₀,?_⟩
  intro N hN B hNB T hT hcut
  obtain ⟨E,hE,hsub,hm,hoff⟩ := hs N hN B hNB T hT hcut
  refine ⟨E,hE,hsub,hm,?_⟩
  intro X hNX hXB P hP Q hQ f hf τ hτ hnot
  have hCount (g : ℕ →* ℝ) (hg : ∀ p : ℕ, p.Prime → |g p| ≤ 1) :
      ‖∑ n ∈ Icc 1 X, ((g n : ℂ)/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ‖ ≤ (ε/2)*(X : ℝ) := by
    have hval : ‖∑ n ∈ Icc 1 X, ((g n : ℂ)/((ValuationDamping.multiplicity P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ‖ ≤ (ε/4)*(X : ℝ) := by
      rw [← CommonDampedSum.twisted_sum_integral X P g τ]
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
        (C := (ε/4)*(X : ℝ)) (fun z hz ↦ by
          have hz' : z ∈ Set.Ioc (0 : ℝ) 1 := by simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hz
          have hzunit : |z| ≤ 1 := by rw [abs_of_nonneg hz'.1.le]; exact hz'.2
          exact hoff X hNX hXB (ValuationDamping.damped P g z)
            (ValuationDamping.damped_prime_bound P g hg z hzunit) τ hτ hnot)
      simpa using hi
    have hd := CountWeightedSum.actual_difference_bound X P (fun p hp ↦ (hP p hp).1) g hg τ
    have hc := CountWeightedSum.square_count_bound P X R hR (fun p hp ↦ (hP p hp).2)
    have hscale := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg X : (0 : ℝ) ≤ X)
    have herr : 2*((PrimeDivisorWeights.squareExceptions P X).card : ℝ) ≤ (ε/4)*(X : ℝ) := by
      calc
        _ ≤ 2*(2*(X : ℝ)/R) := mul_le_mul_of_nonneg_left hc (by norm_num)
        _ = (4/R)*(X : ℝ) := by ring
        _ ≤ _ := hscale
    let A := ∑ n ∈ Icc 1 X, ((g n : ℂ)/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ
    let V := ∑ n ∈ Icc 1 X, ((g n : ℂ)/((ValuationDamping.multiplicity P n+1 : ℕ) : ℂ))*phase (-Real.log (n : ℝ)) τ
    have ht : ‖A‖ ≤ ‖A-V‖+‖V‖ := by simpa only [sub_add_cancel] using norm_add_le (A-V) V
    dsimp only [A,V] at ht
    linarith only [ht,hd,hval,herr]
  have h1 := hCount f hf
  have h2 := hCount (ValuationDamping.damped Q f 0) (ValuationDamping.damped_prime_bound Q f hf 0 (by norm_num))
  rw [CommonPresenceWeightedSum.difference_identity X P Q hQ f τ]
  exact (norm_sub_le _ _).trans (by linarith only [h1,h2])
end PaperP1.CommonUniformWeightedSum
