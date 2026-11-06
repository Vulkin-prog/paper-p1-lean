module

public import PaperP1.Analysis.CeilingAmplificationOrder
public import PaperP1.Analysis.FiniteDyadicAssembly
public import PaperP1.Analysis.PolynomialLongCancellation

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.DyadicLongCutoff
open Finset Filter PaperP1 PolynomialLogarithmicCancellation FiniteDyadicAssembly
open scoped Classical

def count (M : ℕ) : ℕ := CeilingAmplificationOrder.order M 2

theorem count_bound (M : ℕ) : (count M : ℝ) ≤ Real.log (M : ℝ)/Real.log 2+1 := by
  have hh := CeilingAmplificationOrder.logarithmic_upper M 2 (by norm_num)
  change (count M : ℝ)*Real.log 2 ≤ Real.log (M : ℝ)+Real.log 2 at hh
  have hk := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hh
  simpa only [add_div,div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'] using hk

theorem cover (N M : ℕ) (hN : 0 < N) (hM : 0 < M) : M ≤ anchor N (count M) := by
  have hp := CeilingAmplificationOrder.power_lower M hM 2 (by norm_num)
  have hNat : M ≤ (2 : ℕ)^(count M) := by exact_mod_cast hp
  have hMul := Nat.mul_le_mul_left ((2 : ℕ)^(count M)) (show 1 ≤ N by omega)
  simp only [mul_one] at hMul
  exact hNat.trans hMul

theorem anchor_upper (N M : ℕ) (hM : 1 ≤ M) : anchor N (count M) ≤ 2*M*N := by
  have hp := CeilingAmplificationOrder.power_upper M hM 2 (by norm_num)
  have hNat : (2 : ℕ)^(count M) ≤ 2*M := by exact_mod_cast hp
  exact Nat.mul_le_mul_right N hNat

theorem uniform_bound (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ M : ℕ, N ≤ M →
      ∀ t : ℝ, (((2*M*N : ℕ) : ℝ))^a ≤ |t| → |t| ≤ (N : ℝ)^b →
      ∀ σ : ℝ, 0 ≤ σ →
      ‖∑ n ∈ Ico N M, DampedLogarithmicIntegral.integrand σ t n‖ ≤
        (Real.log (M : ℝ)/Real.log 2+1)*constant b/(N : ℝ)^(decay a b) := by
  obtain ⟨N₀,hN₀,hBound⟩ := PolynomialLongCancellation.uniform_span_bound a b ha hb
  refine ⟨N₀,hN₀,?_⟩
  intro N hN M hNM t hLower hUpper σ hσ
  have hNp : 0 < N := by omega
  have hMp : 0 < M := by omega
  have hAnchor : (anchor N (count M) : ℝ) ≤ ((2*M*N : ℕ) : ℝ) := by
    exact_mod_cast anchor_upper N M (show 1 ≤ M by omega)
  have hFrequency := (Real.rpow_le_rpow (Nat.cast_nonneg _) hAnchor ha.le).trans hLower
  have hh := hBound N hN M (count M) hNM (cover N M hNp hMp) t hFrequency hUpper σ hσ
  exact hh.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (count_bound M) (by linarith only [constant_four_le b]))
    (Real.rpow_nonneg (Nat.cast_nonneg N) _))
end PaperP1.DyadicLongCutoff
