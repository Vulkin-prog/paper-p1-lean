module

public import PaperP1.Analysis.FiniteAbelNorm
public import PaperP1.Analysis.DirichletPolynomialMeanValue
public import PaperP1.Analysis.IteratedLogarithmicCorrelation
public import PaperP1.Analysis.PolynomialLogarithmicCancellation
public import PaperP1.Analysis.PolynomialPartialCancellation

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PolynomialDampedCancellation
open Finset Filter PaperP1 PolynomialLogarithmicCancellation
open scoped Classical

def coefficient (σ : ℝ) (n : ℕ) : ℂ := ((n : ℝ)^(-σ) : ℝ)

theorem power_identity (n : ℕ) (hn : 0 < n) (σ : ℝ) :
    coefficient σ n/(n : ℂ) = ((1/(n : ℝ)^(1+σ) : ℝ) : ℂ) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : (n : ℝ)^(-σ)/(n : ℝ)=1/(n : ℝ)^(1+σ) := by
    rw [Real.rpow_add hp,Real.rpow_one,Real.rpow_neg hp.le]
    ring
  unfold coefficient
  exact_mod_cast hh

theorem value_eq_sum_range (X M : ℕ) (hX : 0 < X) (σ t : ℝ) :
    DirichletPolynomialMeanValue.value (Ico X M) (coefficient σ) t =
      ∑ i ∈ range (M-X), LogarithmicExponentialSum.function t ((X+i : ℕ) : ℝ)*
        ((1/((X+i : ℕ) : ℝ)^(1+σ) : ℝ) : ℂ) := by
  unfold DirichletPolynomialMeanValue.value GaussianExponentialSums.polynomial
  rw [sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro i hi
  dsimp only
  rw [power_identity (X+i) (by omega) σ]
  unfold LogarithmicExponentialSum.function
  ring

theorem uniform_bound (a b : ℝ) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^a ≤ |t| → |t| ≤ (X : ℝ)^b →
      ∀ σ : ℝ, 0 ≤ σ → ∀ M, X ≤ M → M ≤ 2*X →
      ‖DirichletPolynomialMeanValue.value (Ico X M) (coefficient σ) t‖ ≤
        constant b/(X : ℝ)^(decay a b+σ) := by
  obtain ⟨X₀,hX₀,hPartial⟩ := PolynomialPartialCancellation.uniform_bound a b
  refine ⟨X₀,hX₀,?_⟩
  intro X hX t hLower hUpper σ hσ M hXM hMX
  have hXpNat : 0 < X := by omega
  have hXp : (0 : ℝ) < X := by exact_mod_cast hXpNat
  have hPrefix : ∀ k ≤ M-X,
      ‖FiniteAbelNorm.partialSum (IteratedLogarithmicCorrelation.sequence [] t X) k‖ ≤
        constant b*(X : ℝ)^(1-decay a b) := by
    intro k hk
    unfold FiniteAbelNorm.partialSum
    rw [IteratedLogarithmicCorrelation.sequence_sum_identity]
    simpa only [IteratedLogarithmicPhase.function_nil] using
      hPartial X hX t hLower hUpper k (by omega)
  have hWeightNN : ∀ k ≤ M-X, 0 ≤ 1/((X+k : ℕ) : ℝ)^(1+σ) := by
    intro k hk
    positivity
  have hWeightMono : ∀ k < M-X,
      1/((X+(k+1) : ℕ) : ℝ)^(1+σ) ≤ 1/((X+k : ℕ) : ℝ)^(1+σ) := by
    intro k hk
    have hp : (0 : ℝ) < (X+k : ℕ) := by exact_mod_cast (show 0 < X+k by omega)
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hp (1+σ))
    exact Real.rpow_le_rpow hp.le (by exact_mod_cast (show X+k ≤ X+(k+1) by omega)) (by linarith only [hσ])
  have hAbel := FiniteAbelNorm.norm_bound (M-X) (IteratedLogarithmicCorrelation.sequence [] t X)
    (fun k ↦ 1/((X+k : ℕ) : ℝ)^(1+σ))
    (constant b*(X : ℝ)^(1-decay a b)) hPrefix hWeightNN hWeightMono
  simp only [Nat.add_zero,IteratedLogarithmicCorrelation.sequence,IteratedLogarithmicPhase.function_nil] at hAbel
  rw [value_eq_sum_range X M hXpNat σ t]
  calc
    _ ≤ (constant b*(X : ℝ)^(1-decay a b))*(1/(X : ℝ)^(1+σ)) := hAbel
    _ = _ := by
      rw [Real.rpow_sub hXp,Real.rpow_one,Real.rpow_add hXp,Real.rpow_one,Real.rpow_add hXp]
      field_simp [hXp.ne',(Real.rpow_pos_of_pos hXp (decay a b)).ne',
        (Real.rpow_pos_of_pos hXp σ).ne']

theorem uniform_undamped_bound (a b : ℝ) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^a ≤ |t| → |t| ≤ (X : ℝ)^b →
      ∀ σ : ℝ, 0 ≤ σ → ∀ M, X ≤ M → M ≤ 2*X →
      ‖DirichletPolynomialMeanValue.value (Ico X M) (coefficient σ) t‖ ≤
        constant b/(X : ℝ)^(decay a b) := by
  obtain ⟨X₀,hX₀,hBound⟩ := uniform_bound a b
  refine ⟨X₀,hX₀,?_⟩
  intro X hX t hLower hUpper σ hσ M hXM hMX
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hPower := Real.rpow_le_rpow_of_exponent_le hXR (show decay a b ≤ decay a b+σ by linarith only [hσ])
  exact (hBound X hX t hLower hUpper σ hσ M hXM hMX).trans
    (div_le_div_of_nonneg_left (by linarith only [constant_four_le b]) (Real.rpow_pos_of_pos hp (decay a b)) hPower)

theorem small_uniform (a b : ℝ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^a ≤ |t| → |t| ≤ (X : ℝ)^b →
      ∀ σ : ℝ, 0 ≤ σ → ∀ M, X ≤ M → M ≤ 2*X →
      ‖DirichletPolynomialMeanValue.value (Ico X M) (coefficient σ) t‖ ≤ ε := by
  obtain ⟨NB,hNB,hBound⟩ := uniform_undamped_bound a b
  have hNat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hInv := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop (decay_pos a b ha)).comp hNat)
  have hZero : Tendsto (fun X : ℕ ↦ constant b/(X : ℝ)^(decay a b)) atTop (nhds 0) := by
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using hInv.const_mul (constant b)
  obtain ⟨NE,hNE⟩ := eventually_atTop.mp ((tendsto_order.mp hZero).2 ε hε)
  refine ⟨max NB NE,by omega,?_⟩
  intro X hX t hLower hUpper σ hσ M hXM hMX
  exact (hBound X (by omega) t hLower hUpper σ hσ M hXM hMX).trans (hNE X (by omega)).le
end PaperP1.PolynomialDampedCancellation
