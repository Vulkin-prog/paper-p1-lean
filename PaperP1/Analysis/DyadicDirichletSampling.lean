module

public import PaperP1.Analysis.CenteredLogarithmicSampling

/-! # Actual dyadic Dirichlet samples with an absolute logarithmic bandwidth -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicDirichletSampling
open Finset PaperP1 DirichletPolynomialMeanValue
open scoped Classical

theorem dyadic_sampled_mean_square {ι : Type*} (R : Finset ι) (τ : ι → ℝ)
    (T : ℝ) (hT : 0 < T) (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r - τ s|)
    (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (hS : S ⊆ Ico N (2*N)) (a : ℕ → ℂ) :
    (∑ r ∈ R, ‖value S a (τ r)‖^2) ≤
      Real.exp 1 * (Real.sqrt Real.pi*(T+1) + 4*Real.pi*(N : ℝ)) *
        (2+(Real.log 2)^2) * ∑ n ∈ S, ‖a n / (n : ℂ)‖^2 := by
  have hh := CenteredLogarithmicSampling.integer_band_sampled_mean_square R τ T hT htau hsep
    S (fun n ↦ a n/(n : ℂ)) N (2*N) hN (by omega)
    (fun n hn ↦ ⟨(mem_Ico.mp (hS hn)).1,(mem_Ico.mp (hS hn)).2.le⟩)
  have hlog : Real.log ((2*N : ℕ) : ℝ)-Real.log N = Real.log 2 := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) (by exact_mod_cast Nat.ne_of_gt hN)]
    ring
  have hc : 2*Real.pi*((2*N : ℕ) : ℝ) = 4*Real.pi*(N : ℝ) := by push_cast; ring
  simpa only [value,hlog,hc] using hh

theorem bounded_dyadic_sampled_mean_square {ι : Type*} (R : Finset ι) (τ : ι → ℝ)
    (T : ℝ) (hT : 0 < T) (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r - τ s|)
    (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (hS : S ⊆ Ico N (2*N))
    (a : ℕ → ℂ) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) :
    (∑ r ∈ R, ‖value S a (τ r)‖^2) ≤
      Real.exp 1 * (Real.sqrt Real.pi*(T+1)/(N : ℝ) + 4*Real.pi) *
        (2+(Real.log 2)^2) := by
  have hh := dyadic_sampled_mean_square R τ T hT htau hsep N hN S hS a
  have hc := unit_coefficient_square_budget N hN S hS a ha
  have hb := hh.trans (mul_le_mul_of_nonneg_left hc (by positivity))
  calc
    _ ≤ Real.exp 1*(Real.sqrt Real.pi*(T+1)+4*Real.pi*(N : ℝ)) *
        (2+(Real.log 2)^2) * (1/(N : ℝ)) := hb
    _ = _ := by field_simp
end DyadicDirichletSampling
