module

public import PaperP1.Analysis.TerminalLogarithmicBudget
public import PaperP1.Analysis.RecursiveLogarithmicDifferencing
public import PaperP1.Analysis.IteratedLogarithmicCorrelation
public import PaperP1.Analysis.ActualLogarithmicPower
public import PaperP1.Analysis.FixedOrderLogarithmicScale
public import PaperP1.Analysis.RecursiveBudgetPower
public import PaperP1.Analysis.RoundedLogarithmicParameters
public import PaperP1.Analysis.RoundedTerminalDecay

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PartialLogarithmicPower
open Finset Filter PaperP1 FixedOrderLogarithmicScale RoundedLogarithmicParameters
open scoped Classical

theorem uniform_bound (n : ℕ) (hn : 0 < n) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^(3/4 : ℝ) ≤ |t| → |t| ≤ (X : ℝ)^((n : ℝ)+1/4) →
      ∀ L ≤ X, ‖∑ j ∈ Ico X (X+L), LogarithmicExponentialSum.function t j‖ ≤
        ActualLogarithmicPower.constant n*(X : ℝ)^(1-ActualLogarithmicPower.decay n) := by
  obtain ⟨NG,hG⟩ := eventually_atTop.mp (geometry_eventually n hn)
  obtain ⟨NB,hNB,hBudget⟩ := RoundedTerminalDecay.uniform_budget_bound n hn
  refine ⟨max NB NG,by omega,?_⟩
  intro X hX t hLower hUpper L hLX
  obtain ⟨hX1,hK,hKHalf,hKUpper,hAll⟩ := hG X (by omega)
  obtain ⟨ht,hA,hHalf,hAUpper,hAK,hSpan⟩ := hAll t hLower hUpper
  have hXpNat : 0 < X := by omega
  have hXp : (0 : ℝ) < X := by exact_mod_cast hXpNat
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hAp : 0 < step n X t := by omega
  have hKp : 0 < count n X := by omega
  have htne : t ≠ 0 := abs_pos.mp ht
  let A := step n X t
  let K := count n X
  let e := TerminalLogarithmicBudget.budget X A K n t
  have he0 : 0 ≤ e := TerminalLogarithmicBudget.budget_nonneg X A K n t
  have hLeaf : ∀ us : List ℝ, us.length=n →
      (∀ h ∈ us, (A : ℝ) ≤ h ∧ h ≤ ((A*K : ℕ) : ℝ)) →
      ∀ M ≤ X, ‖∑ j ∈ range M, IteratedLogarithmicCorrelation.sequence (us++[]) t X j‖ ≤ (X : ℝ)*e := by
    intro us hLen hUs M hMX
    have hh := TerminalLogarithmicBudget.leaf_bound X A K n hXpNat hAp hKp hSpan t htne us hLen hUs M hMX
    simpa only [List.append_nil,IteratedLogarithmicCorrelation.sequence_sum_identity] using hh
  have hIter := RecursiveLogarithmicDifferencing.iterate_bound X A K hAp hKp hAK t e he0 n [] hLeaf L hLX
  rw [IteratedLogarithmicCorrelation.sequence_sum_identity] at hIter
  simp only [IteratedLogarithmicPhase.function_nil] at hIter
  have heBound : e ≤ ActualLogarithmicPower.constant n*(X : ℝ)^(-(exponent n)) :=
    (hBudget X (by omega) t hLower hUpper).trans (ActualLogarithmicPower.envelope_bound n X hn hX1)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hBetaNN : 0 ≤ exponent n := by unfold exponent; positivity
  have hPower := RecursiveBudgetPower.bound K n X (exponent n) (ActualLogarithmicPower.constant n)
    e hXR hBetaNN (ActualLogarithmicPower.constant_four_le n) hKHalf he0 heBound
  have hExp : -(exponent n)/(2 : ℝ)^n=-(ActualLogarithmicPower.decay n) := by
    unfold ActualLogarithmicPower.decay
    ring
  rw [hExp] at hPower
  calc
    _ ≤ (X : ℝ)*(ActualLogarithmicPower.constant n*(X : ℝ)^(-(ActualLogarithmicPower.decay n))) :=
      hIter.trans (mul_le_mul_of_nonneg_left hPower (Nat.cast_nonneg X))
    _ = ActualLogarithmicPower.constant n*((X : ℝ)^(1 : ℝ)*(X : ℝ)^(-(ActualLogarithmicPower.decay n))) := by
      rw [Real.rpow_one]
      ring
    _ = _ := by
      simpa only [sub_eq_add_neg] using congrArg (fun z : ℝ ↦ ActualLogarithmicPower.constant n*z)
        (Real.rpow_add hXp (1 : ℝ) (-(ActualLogarithmicPower.decay n))).symm

theorem relative_bound (n : ℕ) (hn : 0 < n) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^(3/4 : ℝ) ≤ |t| → |t| ≤ (X : ℝ)^((n : ℝ)+1/4) →
      ∀ L ≤ X, ‖∑ j ∈ Ico X (X+L), LogarithmicExponentialSum.function t j‖/(X : ℝ) ≤
        ActualLogarithmicPower.constant n/(X : ℝ)^(ActualLogarithmicPower.decay n) := by
  obtain ⟨X₀,hX₀,hBound⟩ := uniform_bound n hn
  refine ⟨X₀,hX₀,?_⟩
  intro X hX t hLower hUpper L hLX
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  calc
    _ ≤ (ActualLogarithmicPower.constant n*(X : ℝ)^(1-ActualLogarithmicPower.decay n))/(X : ℝ) :=
      div_le_div_of_nonneg_right (hBound X hX t hLower hUpper L hLX) (Nat.cast_nonneg X)
    _ = _ := by
      rw [Real.rpow_sub hXp,Real.rpow_one]
      field_simp [hXp.ne',(Real.rpow_pos_of_pos hXp (ActualLogarithmicPower.decay n)).ne']
end PaperP1.PartialLogarithmicPower
