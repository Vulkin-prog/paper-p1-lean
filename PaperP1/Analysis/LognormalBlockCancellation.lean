module

public import PaperP1.Analysis.PolynomialPartialCancellation
public import PaperP1.Analysis.IteratedLogarithmicCorrelation
public import PaperP1.Analysis.FiniteAbelVariation
public import PaperP1.Analysis.LognormalSieveWeight
public import PaperP1.Analysis.LognormalWeightVariation

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalBlockCancellation
open Finset Filter PaperP1 PolynomialLogarithmicCancellation LognormalSieveWeight
open scoped Classical

theorem phase_prefix_identity (N L : ℕ) (t : ℝ) :
    (∑ i ∈ range L, LogarithmicExponentialSum.function t ((N+i : ℕ) : ℝ))=
      ∑ n ∈ Ico N (N+L), LogarithmicExponentialSum.function t n := by
  rw [sum_Ico_eq_sum_range,Nat.add_sub_cancel_left]

theorem uniform_bound (a b : ℝ) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ t : ℝ,
      (N : ℝ)^a ≤ |t| → |t| ≤ (N : ℝ)^b → ∀ A : ℝ, 0 < A → ∀ L ≤ N,
      ‖∑ n ∈ Ico N (N+L), LogarithmicExponentialSum.function t n*(weight A n : ℂ)‖ ≤
        (1+LognormalWeightVariation.constant)*constant b*A/(N : ℝ)^(decay a b) := by
  obtain ⟨N₀,hN₀,hPhase⟩ := PolynomialPartialCancellation.uniform_bound a b
  refine ⟨N₀,hN₀,?_⟩
  intro N hN t hLower hUpper A hA L hLN
  have hNP : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let aN := fun i : ℕ ↦ LogarithmicExponentialSum.function t ((N+i : ℕ) : ℝ)
  let wN := fun i : ℕ ↦ (weight A ((N+i : ℕ) : ℝ) : ℂ)
  let D : ℝ := constant b*(N : ℝ)^(1-decay a b)
  let C := LognormalWeightVariation.constant
  have hCP : 0 < C := LognormalWeightVariation.constant_pos
  have hD : 0 ≤ D := mul_nonneg (by linarith only [constant_four_le b]) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hPartial : ∀ k ≤ L, ‖FiniteAbelNorm.partialSum aN k‖ ≤ D := by
    intro k hk
    unfold FiniteAbelNorm.partialSum
    rw [phase_prefix_identity]
    exact hPhase N hN t hLower hUpper k (by omega)
  have hLast : ‖wN L‖ ≤ A/(N : ℝ) := by
    dsimp only [wN]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos A _)]
    have hNL : (N : ℝ) ≤ ((N+L : ℕ) : ℝ) := by exact_mod_cast (show N ≤ N+L by omega)
    exact (LognormalWeightVariation.weight_le_ratio A _ hA (hNP.trans_le hNL)).trans
      (div_le_div_of_nonneg_left hA.le hNP hNL)
  have hVariation : ∀ k < L, ‖wN k-wN (k+1)‖ ≤ C*A/(N : ℝ)^2 := by
    intro k hk
    dsimp only [wN]
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    have hNk : (N : ℝ) ≤ ((N+k : ℕ) : ℝ) := by exact_mod_cast (show N ≤ N+k by omega)
    have hStep := LognormalWeightVariation.local_variation A ((N+k : ℕ) : ℝ) ((N+(k+1) : ℕ) : ℝ)
      hA (hNP.trans_le hNk) (by constructor <;> push_cast <;> linarith)
    rw [abs_sub_comm] at hStep
    exact hStep.trans (div_le_div_of_nonneg_left (mul_nonneg hCP.le hA.le) (sq_pos_of_pos hNP)
      (pow_le_pow_left₀ hNP.le hNk 2))
  have hh := FiniteAbelVariation.difference_bound L aN wN D (A/(N : ℝ)) (C*A/(N : ℝ)^2)
    hPartial hLast hVariation
  have hVar : A/(N : ℝ)+(L : ℝ)*(C*A/(N : ℝ)^2) ≤ (1+C)*A/(N : ℝ) := by
    have hTerm := mul_le_mul_of_nonneg_right (by exact_mod_cast hLN : (L : ℝ) ≤ N) (by positivity : 0 ≤ C*A/(N : ℝ)^2)
    have he : A/(N : ℝ)+(N : ℝ)*(C*A/(N : ℝ)^2)=(1+C)*A/(N : ℝ) := by field_simp
    exact (add_le_add (le_refl _) hTerm).trans_eq he
  have hSum : (∑ n ∈ Ico N (N+L), LogarithmicExponentialSum.function t n*(weight A n : ℂ))=
      ∑ i ∈ range L, aN i*wN i := by rw [sum_Ico_eq_sum_range,Nat.add_sub_cancel_left]
  rw [hSum]
  calc
    _ ≤ D*((1+C)*A/(N : ℝ)) := hh.trans (mul_le_mul_of_nonneg_left hVar hD)
    _ = _ := by
      dsimp only [D,C]
      rw [Real.rpow_sub hNP,Real.rpow_one]
      field_simp [hNP.ne',(Real.rpow_pos_of_pos hNP (decay a b)).ne']
end PaperP1.LognormalBlockCancellation
