module

public import PaperP1.Analysis.DampedLogarithmicIntegral
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import PaperP1.Analysis.DampedDirichletTail

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ActualZetaTail
open Finset Filter MeasureTheory PaperP1 DampedLogarithmicIntegral
open scoped Classical

def argument (σ t : ℝ) : ℂ := ((1+σ : ℝ) : ℂ)+Complex.I*(t : ℂ)

theorem argument_re (σ t : ℝ) : (argument σ t).re=1+σ := by simp [argument]

theorem phase_eq_cpow (t x : ℝ) (hx : 0 < x) :
    LogarithmicExponentialSum.function t x=(x : ℂ)^(-Complex.I*(t : ℂ)) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [LogarithmicExponentialSum.function,LogarithmicPhase.phase,
    Complex.cpow_def_of_ne_zero hxC,← Complex.ofReal_log hx.le]
  congr 1
  push_cast
  ring

theorem integrand_eq_cpow (σ t x : ℝ) (hx : 0 < x) :
    integrand σ t x=1/(x : ℂ)^(argument σ t) := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [integrand,numerator,Complex.ofReal_cpow hx.le,phase_eq_cpow t x hx,
    ← Complex.cpow_add _ _ hxC]
  calc
    _ = (x : ℂ)^(((-σ : ℝ) : ℂ)+(-Complex.I*(t : ℂ)))/(x : ℂ)^(1 : ℂ) := by rw [Complex.cpow_one]
    _ = (x : ℂ)^((((-σ : ℝ) : ℂ)+(-Complex.I*(t : ℂ)))-1) :=
      (Complex.cpow_sub _ _ hxC).symm
    _ = (x : ℂ)^(-(argument σ t)) := by congr 1; unfold argument; push_cast; ring
    _ = _ := by rw [Complex.cpow_neg,one_div]

theorem nat_integrand_eq_cpow (σ t : ℝ) (hσ : 0 < σ) (n : ℕ) :
    integrand σ t n=1/(n : ℂ)^(argument σ t) := by
  by_cases hn : n=0
  · subst n
    have hArg : argument σ t ≠ 0 := by
      intro h
      have hh := congrArg Complex.re h
      rw [argument_re] at hh
      simp only [Complex.zero_re] at hh
      linarith only [hσ,hh]
    simp [integrand,Complex.zero_cpow hArg]
  · simpa only [Complex.ofReal_natCast] using integrand_eq_cpow σ t n (by exact_mod_cast Nat.pos_of_ne_zero hn)

theorem series_eq_zeta (σ t : ℝ) (hσ : 0 < σ) :
    DampedDirichletTail.series σ t=riemannZeta (argument σ t) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by rw [argument_re]; linarith only [hσ])]
  unfold DampedDirichletTail.series
  exact tsum_congr (nat_integrand_eq_cpow σ t hσ)

theorem zeta_difference_bound (σ t : ℝ) (hσ : 0 < σ) (ht : t ≠ 0)
    (N : ℕ) (hN : 0 < N) :
    ‖riemannZeta (argument σ t)-(∑ n ∈ range N, integrand σ t n)‖ ≤
      2*(N : ℝ)^(-σ)/|t|+2*(1+σ+|t|)*(N : ℝ)^(-σ)/(N : ℝ) := by
  rw [← series_eq_zeta σ t hσ]
  exact DampedDirichletTail.series_difference_bound σ t hσ ht N hN
end PaperP1.ActualZetaTail
