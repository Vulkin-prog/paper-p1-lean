module

public import PaperP1.Analysis.PolynomialDampedCancellation
public import PaperP1.Analysis.DampedLogarithmicIntegral
public import PaperP1.Analysis.FiniteDyadicAssembly

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PolynomialLongCancellation
open Finset Filter PaperP1 PolynomialLogarithmicCancellation FiniteDyadicAssembly
open scoped Classical

theorem value_eq_sum (N M : ℕ) (σ t : ℝ) :
    DirichletPolynomialMeanValue.value (Ico N M) (PolynomialDampedCancellation.coefficient σ) t=
      ∑ n ∈ Ico N M, DampedLogarithmicIntegral.integrand σ t n := by
  unfold DirichletPolynomialMeanValue.value GaussianExponentialSums.polynomial
  apply sum_congr rfl
  intro n hn
  unfold PolynomialDampedCancellation.coefficient DampedLogarithmicIntegral.integrand
    DampedLogarithmicIntegral.numerator LogarithmicExponentialSum.function
  push_cast
  ring

theorem uniform_blockwise_bound (a b : ℝ) (ha : 0 < a) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ M K : ℕ, X ≤ M → M ≤ anchor X K →
      ∀ t : ℝ, (∀ j < K, (anchor X j : ℝ)^a ≤ |t| ∧ |t| ≤ (anchor X j : ℝ)^b) →
      ∀ σ : ℝ, 0 ≤ σ →
      ‖∑ n ∈ Ico X M, DampedLogarithmicIntegral.integrand σ t n‖ ≤
        (K : ℝ)*constant b/(X : ℝ)^(decay a b) := by
  obtain ⟨X₀,hX₀,hBlock⟩ := PolynomialDampedCancellation.uniform_undamped_bound a b
  refine ⟨X₀,hX₀,?_⟩
  intro X hX M K hXM hCover t hFrequency σ hσ
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hD : 0 ≤ constant b/(X : ℝ)^(decay a b) := by
    exact div_nonneg (by linarith only [constant_four_le b]) (Real.rpow_nonneg (Nat.cast_nonneg X) _)
  have hActual := constant_norm_bound X M K hXM hCover
    (fun n ↦ DampedLogarithmicIntegral.integrand σ t n)
    (constant b/(X : ℝ)^(decay a b)) hD (by
      intro j hj U hAU hU2
      have hAX := anchor_lower X j
      have hAj : X₀ ≤ anchor X j := by omega
      have hh := hBlock (anchor X j) hAj t (hFrequency j hj).1 (hFrequency j hj).2 σ hσ U hAU hU2
      rw [value_eq_sum] at hh
      have hPow := Real.rpow_le_rpow hXp.le (by exact_mod_cast hAX : (X : ℝ) ≤ anchor X j) (decay_pos a b ha).le
      exact hh.trans (div_le_div_of_nonneg_left (by linarith only [constant_four_le b])
        (Real.rpow_pos_of_pos hXp (decay a b)) hPow))
  exact hActual.trans_eq (by ring)

theorem uniform_span_bound (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ M K : ℕ, X ≤ M → M ≤ anchor X K →
      ∀ t : ℝ, (anchor X K : ℝ)^a ≤ |t| → |t| ≤ (X : ℝ)^b →
      ∀ σ : ℝ, 0 ≤ σ →
      ‖∑ n ∈ Ico X M, DampedLogarithmicIntegral.integrand σ t n‖ ≤
        (K : ℝ)*constant b/(X : ℝ)^(decay a b) := by
  obtain ⟨X₀,hX₀,hBound⟩ := uniform_blockwise_bound a b ha
  refine ⟨X₀,hX₀,?_⟩
  intro X hX M K hXM hCover t hLower hUpper σ hσ
  apply hBound X hX M K hXM hCover t _ σ hσ
  intro j hj
  have hAnchor : (anchor X j : ℝ) ≤ anchor X K := by exact_mod_cast anchor_mono X (show j ≤ K by omega)
  have hBase : (X : ℝ) ≤ anchor X j := by exact_mod_cast anchor_lower X j
  exact ⟨(Real.rpow_le_rpow (Nat.cast_nonneg _) hAnchor ha.le).trans hLower,
    hUpper.trans (Real.rpow_le_rpow (Nat.cast_nonneg X) hBase hb)⟩
end PaperP1.PolynomialLongCancellation
