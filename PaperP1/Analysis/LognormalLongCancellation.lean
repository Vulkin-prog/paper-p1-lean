module

public import PaperP1.Analysis.LognormalBlockCancellation
public import PaperP1.Analysis.LognormalPhaseVariation
public import PaperP1.Analysis.FiniteDyadicAssembly
public import PaperP1.Analysis.DyadicLongCutoff

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalLongCancellation
open Finset Filter PaperP1 PolynomialLogarithmicCancellation FiniteDyadicAssembly
open scoped Classical

def coefficient (b : ℝ) : ℝ := (1+LognormalWeightVariation.constant)*constant b

theorem coefficient_pos (b : ℝ) : 0 < coefficient b := by
  have hC := LognormalWeightVariation.constant_pos
  have hB := constant_four_le b
  unfold coefficient
  positivity

theorem sum_identity (A t : ℝ) (N M : ℕ) :
    (∑ n ∈ Ico N M, LognormalPhaseVariation.function A t n)=
      ∑ n ∈ Ico N M, LogarithmicExponentialSum.function t n*(LognormalSieveWeight.weight A n : ℂ) := by
  apply sum_congr rfl
  intro n hn
  exact mul_comm _ _

theorem uniform_blockwise_bound (a b : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ M K : ℕ, N ≤ M → M ≤ anchor N K →
      ∀ t : ℝ, (∀ j < K, (anchor N j : ℝ)^a ≤ |t| ∧ |t| ≤ (anchor N j : ℝ)^b) →
      ∀ A : ℝ, 0 < A →
      ‖∑ n ∈ Ico N M, LognormalPhaseVariation.function A t n‖ ≤
        (K : ℝ)*coefficient b*A/(N : ℝ)^(decay a b) := by
  obtain ⟨N₀,hN₀,hBlock⟩ := LognormalBlockCancellation.uniform_bound a b
  refine ⟨N₀,hN₀,?_⟩
  intro N hN M K hNM hCover t hFrequency A hA
  have hNP : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNumerator : 0 ≤ coefficient b*A := mul_nonneg (coefficient_pos b).le hA.le
  have hD : 0 ≤ coefficient b*A/(N : ℝ)^(decay a b) := div_nonneg hNumerator (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hActual := constant_norm_bound N M K hNM hCover
    (fun n ↦ LognormalPhaseVariation.function A t n) (coefficient b*A/(N : ℝ)^(decay a b)) hD (by
      intro j hj U hJU hU2
      have hJN := anchor_lower N j
      have hLength : U-anchor N j ≤ anchor N j := by omega
      have hh := hBlock (anchor N j) (by omega) t (hFrequency j hj).1 (hFrequency j hj).2 A hA (U-anchor N j) hLength
      rw [Nat.add_sub_of_le hJU,← sum_identity] at hh
      change ‖∑ n ∈ Ico (anchor N j) U, LognormalPhaseVariation.function A t n‖ ≤
        (coefficient b*A)/(anchor N j : ℝ)^(decay a b) at hh
      have hPower := Real.rpow_le_rpow hNP.le (by exact_mod_cast hJN : (N : ℝ) ≤ anchor N j) (decay_pos a b ha).le
      exact hh.trans (div_le_div_of_nonneg_left hNumerator (Real.rpow_pos_of_pos hNP _) hPower))
  exact hActual.trans_eq (by ring)

theorem uniform_span_bound (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ M K : ℕ, N ≤ M → M ≤ anchor N K →
      ∀ t : ℝ, (anchor N K : ℝ)^a ≤ |t| → |t| ≤ (N : ℝ)^b →
      ∀ A : ℝ, 0 < A →
      ‖∑ n ∈ Ico N M, LognormalPhaseVariation.function A t n‖ ≤
        (K : ℝ)*coefficient b*A/(N : ℝ)^(decay a b) := by
  obtain ⟨N₀,hN₀,hBound⟩ := uniform_blockwise_bound a b ha
  refine ⟨N₀,hN₀,?_⟩
  intro N hN M K hNM hCover t hLower hUpper A hA
  apply hBound N hN M K hNM hCover t _ A hA
  intro j hj
  have hAnchor : (anchor N j : ℝ) ≤ anchor N K := by exact_mod_cast anchor_mono N (show j ≤ K by omega)
  have hBase : (N : ℝ) ≤ anchor N j := by exact_mod_cast anchor_lower N j
  exact ⟨(Real.rpow_le_rpow (Nat.cast_nonneg _) hAnchor ha.le).trans hLower,
    hUpper.trans (Real.rpow_le_rpow (Nat.cast_nonneg N) hBase hb)⟩

theorem uniform_bound (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ M : ℕ, N ≤ M →
      ∀ t : ℝ, (((2*M*N : ℕ) : ℝ))^a ≤ |t| → |t| ≤ (N : ℝ)^b →
      ∀ A : ℝ, 0 < A →
      ‖∑ n ∈ Ico N M, LognormalPhaseVariation.function A t n‖ ≤
        (Real.log (M : ℝ)/Real.log 2+1)*coefficient b*A/(N : ℝ)^(decay a b) := by
  obtain ⟨N₀,hN₀,hBound⟩ := uniform_span_bound a b ha hb
  refine ⟨N₀,hN₀,?_⟩
  intro N hN M hNM t hLower hUpper A hA
  have hNP : 0 < N := by omega
  have hMP : 0 < M := by omega
  have hAnchor : (anchor N (DyadicLongCutoff.count M) : ℝ) ≤ ((2*M*N : ℕ) : ℝ) := by
    exact_mod_cast DyadicLongCutoff.anchor_upper N M (show 1 ≤ M by omega)
  have hFrequency := (Real.rpow_le_rpow (Nat.cast_nonneg _) hAnchor ha.le).trans hLower
  have hh := hBound N hN M (DyadicLongCutoff.count M) hNM (DyadicLongCutoff.cover N M hNP hMP)
    t hFrequency hUpper A hA
  exact hh.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (DyadicLongCutoff.count_bound M) (coefficient_pos b).le) hA.le)
    (Real.rpow_nonneg (Nat.cast_nonneg N) _))
end PaperP1.LognormalLongCancellation
