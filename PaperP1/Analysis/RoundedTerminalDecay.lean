module

public import PaperP1.Analysis.TerminalLogarithmicBudget
public import PaperP1.Analysis.RecursiveLogarithmicDifferencing
public import PaperP1.Analysis.FixedOrderFirstTermDecay
public import PaperP1.Analysis.FixedOrderLogarithmicScale
public import PaperP1.Analysis.FixedOrderSecondTermDecay
public import PaperP1.Analysis.RoundedLogarithmicParameters

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.RoundedTerminalDecay
open Finset Filter PaperP1 RoundedLogarithmicParameters
open scoped Classical

def envelope (n X : ℕ) : ℝ := (6 : ℝ)^(n+1)/(X : ℝ)^(1/2 : ℝ)+(n.factorial : ℝ)/(X : ℝ)^(7/16 : ℝ)

theorem envelope_nonneg (n X : ℕ) : 0 ≤ envelope n X := by unfold envelope; positivity

theorem envelope_tendsto (n : ℕ) : Tendsto (envelope n) atTop (nhds 0) := by
  change Tendsto (fun X : ℕ ↦ (6 : ℝ)^(n+1)/(X : ℝ)^(1/2 : ℝ)+(n.factorial : ℝ)/(X : ℝ)^(7/16 : ℝ)) atTop (nhds 0)
  have hNat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hHalf := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp hNat)
  have hSeven := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7/16)).comp hNat)
  have hh := (hHalf.const_mul ((6 : ℝ)^(n+1))).add (hSeven.const_mul (n.factorial : ℝ))
  simpa only [Function.comp_def,div_eq_mul_inv,mul_zero,add_zero] using hh

theorem budget_bound (n X A K : ℕ) (hn : 0 < n) (hX : 1 ≤ X) (t : ℝ) (ht : 0 < |t|)
    (hHalf : FixedOrderLogarithmicScale.scale n X |t|/2 ≤ (A : ℝ))
    (hA : (A : ℝ) ≤ FixedOrderLogarithmicScale.scale n X |t|)
    (hK : (K : ℝ) ≤ (X : ℝ)^(FixedOrderLogarithmicScale.exponent n)) :
    TerminalLogarithmicBudget.budget X A K n t ≤ envelope n X := by
  exact add_le_add (FixedOrderFirstTermDecay.first_bound n X A hn hX t ht hHalf)
    (FixedOrderSecondTermDecay.second_bound n X A K hn hX t ht hA hK)

theorem uniform_budget_bound (n : ℕ) (hn : 0 < n) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^(3/4 : ℝ) ≤ |t| → |t| ≤ (X : ℝ)^((n : ℝ)+1/4) →
      TerminalLogarithmicBudget.budget X (step n X t) (count n X) n t ≤ envelope n X := by
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp (geometry_eventually n hn)
  refine ⟨max 1 X₀,by omega,?_⟩
  intro X hX t hLower hUpper
  obtain ⟨hX1,hK,hKHalf,hKUpper,hAll⟩ := hX₀ X (by omega)
  obtain ⟨ht,hA,hHalf,hAUpper,hAK,hSpan⟩ := hAll t hLower hUpper
  exact budget_bound n X (step n X t) (count n X) hn hX1 t ht hHalf hAUpper hKUpper

theorem uniform_logarithmic_bound (n : ℕ) (hn : 0 < n) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^(3/4 : ℝ) ≤ |t| → |t| ≤ (X : ℝ)^((n : ℝ)+1/4) →
      ‖∑ j ∈ Ico X (2*X), LogarithmicExponentialSum.function t j‖ ≤
        (X : ℝ)*RecursiveLogarithmicDifferencing.budget (count n X) n (envelope n X) := by
  obtain ⟨NG,hG⟩ := eventually_atTop.mp (geometry_eventually n hn)
  obtain ⟨NB,hNB,hBudget⟩ := uniform_budget_bound n hn
  refine ⟨max NB NG,by omega,?_⟩
  intro X hX t hLower hUpper
  obtain ⟨hX1,hK,hKHalf,hKUpper,hAll⟩ := hG X (by omega)
  obtain ⟨ht,hA,hHalf,hAUpper,hAK,hSpan⟩ := hAll t hLower hUpper
  have htne : t ≠ 0 := abs_pos.mp ht
  have hRaw := TerminalLogarithmicBudget.logarithmic_bound X (step n X t) (count n X) n
    (by omega) (by omega) (by omega) hAK hSpan t htne
  have hMono := RecursiveLogarithmicDifferencing.budget_monotone (count n X) n _ _
    (hBudget X (by omega) t hLower hUpper)
  exact hRaw.trans (mul_le_mul_of_nonneg_left hMono (Nat.cast_nonneg X))

theorem small_uniform (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^(3/4 : ℝ) ≤ |t| → |t| ≤ (X : ℝ)^((n : ℝ)+1/4) →
      ‖∑ j ∈ Ico X (2*X), LogarithmicExponentialSum.function t j‖ ≤ ε*(X : ℝ) := by
  obtain ⟨NB,hNB,hBound⟩ := uniform_logarithmic_bound n hn
  have hLim := RecursiveLogarithmicDifferencing.budget_tendsto n (count n) (count_tendsto n hn)
    (envelope n) (envelope_tendsto n)
  obtain ⟨NL,hL⟩ := eventually_atTop.mp (hLim.eventually (eventually_lt_nhds hε))
  refine ⟨max NB NL,by omega,?_⟩
  intro X hX t hLower hUpper
  have hh := hBound X (by omega) t hLower hUpper
  have hSmall := mul_le_mul_of_nonneg_left (hL X (by omega)).le (Nat.cast_nonneg X : (0 : ℝ) ≤ X)
  exact hh.trans (hSmall.trans_eq (by ring))
end PaperP1.RoundedTerminalDecay
