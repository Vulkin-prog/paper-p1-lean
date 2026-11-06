module

public import PaperP1.Analysis.CommonPresenceWeightedSum
public import PaperP1.Analysis.UniformCountWeightedTwistedSum

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UniformPresenceWeightedSum
open Finset Filter PaperP1
open scoped Classical

theorem uniform_bound (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ R : ℝ, 2 ≤ R ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ X ≥ X₀,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ R < (p : ℝ)) →
      ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) →
      ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      ∀ τ : ℝ, T₀ ≤ |τ| → |τ| ≤ (X : ℝ)^B →
      ‖CommonPresenceWeightedSum.weighted X P Q f τ‖ ≤ ε*(X : ℝ) := by
  obtain ⟨R,hR,T₀,hT₀,X₀,hX₀,hBound⟩ := UniformCountWeightedTwistedSum.count_uniform_bound B (ε/2) hB (by positivity)
  refine ⟨R,hR,T₀,hT₀,X₀,hX₀,?_⟩
  intro X hX P hP Q hQ f hf τ hLower hUpper
  have hFirst := hBound X hX P hP f hf τ hLower hUpper
  have hSecond := hBound X hX P hP (ValuationDamping.damped Q f 0)
    (ValuationDamping.damped_prime_bound Q f hf 0 (by norm_num)) τ hLower hUpper
  rw [CommonPresenceWeightedSum.difference_identity X P Q hQ f τ]
  exact (norm_sub_le _ _).trans (by linarith only [hFirst,hSecond])
end PaperP1.UniformPresenceWeightedSum
