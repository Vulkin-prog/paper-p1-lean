module

public import PaperP1.Analysis.FiniteAbelNorm
public import PaperP1.Analysis.DirichletPolynomialMeanValue
public import PaperP1.Analysis.IteratedLogarithmicCorrelation
public import PaperP1.Analysis.PolynomialLogarithmicCancellation
public import PaperP1.Analysis.PolynomialPartialCancellation

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PolynomialWeightedCancellation
open Finset Filter PaperP1 PolynomialLogarithmicCancellation
open scoped Classical

theorem value_eq_sum_range (X M : ℕ) (t : ℝ) :
    DirichletPolynomialMeanValue.value (Ico X M) (fun _ ↦ 1) t =
      ∑ i ∈ range (M-X), LogarithmicExponentialSum.function t ((X+i : ℕ) : ℝ)/((X+i : ℕ) : ℂ) := by
  unfold DirichletPolynomialMeanValue.value GaussianExponentialSums.polynomial
  rw [sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro i hi
  unfold LogarithmicExponentialSum.function
  ring

theorem uniform_bound (a b : ℝ) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^a ≤ |t| → |t| ≤ (X : ℝ)^b →
      ∀ M, X ≤ M → M ≤ 2*X →
      ‖DirichletPolynomialMeanValue.value (Ico X M) (fun _ ↦ 1) t‖ ≤
        constant b/(X : ℝ)^(decay a b) := by
  obtain ⟨X₀,hX₀,hPartial⟩ := PolynomialPartialCancellation.uniform_bound a b
  refine ⟨X₀,hX₀,?_⟩
  intro X hX t hLower hUpper M hXM hMX
  have hXpNat : 0 < X := by omega
  have hXp : (0 : ℝ) < X := by exact_mod_cast hXpNat
  have hLen : M-X ≤ X := by omega
  have hPrefix : ∀ k ≤ M-X,
      ‖FiniteAbelNorm.partialSum (IteratedLogarithmicCorrelation.sequence [] t X) k‖ ≤
        constant b*(X : ℝ)^(1-decay a b) := by
    intro k hk
    unfold FiniteAbelNorm.partialSum
    rw [IteratedLogarithmicCorrelation.sequence_sum_identity]
    simpa only [IteratedLogarithmicPhase.function_nil] using
      hPartial X hX t hLower hUpper k (by omega)
  have hAbel := FiniteAbelNorm.reciprocal_norm_bound X (M-X) hXpNat
    (IteratedLogarithmicCorrelation.sequence [] t X)
    (constant b*(X : ℝ)^(1-decay a b)) hPrefix
  rw [value_eq_sum_range]
  have hEq : (∑ i ∈ range (M-X), IteratedLogarithmicCorrelation.sequence [] t X i/((X+i : ℕ) : ℂ)) =
      ∑ i ∈ range (M-X), LogarithmicExponentialSum.function t ((X+i : ℕ) : ℝ)/((X+i : ℕ) : ℂ) := by
    simp only [IteratedLogarithmicCorrelation.sequence,IteratedLogarithmicPhase.function_nil]
  rw [hEq] at hAbel
  calc
    _ ≤ (constant b*(X : ℝ)^(1-decay a b))/(X : ℝ) := hAbel
    _ = _ := by
      rw [Real.rpow_sub hXp,Real.rpow_one]
      field_simp [hXp.ne',(Real.rpow_pos_of_pos hXp (decay a b)).ne']

theorem small_uniform (a b : ℝ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^a ≤ |t| → |t| ≤ (X : ℝ)^b →
      ∀ M, X ≤ M → M ≤ 2*X →
      ‖DirichletPolynomialMeanValue.value (Ico X M) (fun _ ↦ 1) t‖ ≤ ε := by
  obtain ⟨NB,hNB,hBound⟩ := uniform_bound a b
  have hNat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hInv := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (decay_pos a b ha)).comp hNat)
  have hZero : Tendsto (fun X : ℕ ↦ constant b/(X : ℝ)^(decay a b)) atTop (nhds 0) := by
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using hInv.const_mul (constant b)
  obtain ⟨NE,hNE⟩ := eventually_atTop.mp ((tendsto_order.mp hZero).2 ε hε)
  refine ⟨max NB NE,by omega,?_⟩
  intro X hX t hLower hUpper M hXM hMX
  exact (hBound X (by omega) t hLower hUpper M hXM hMX).trans (hNE X (by omega)).le
end PaperP1.PolynomialWeightedCancellation
