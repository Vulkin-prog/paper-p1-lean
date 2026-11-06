module

public import PaperP1.Analysis.ActualZetaTail
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import PaperP1.Analysis.DampedFiniteEulerExtension
public import PaperP1.Analysis.RealEulerDamping

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.DampedEulerZetaComparison
open Finset Filter PaperP1
open scoped Classical

theorem unit_product_tendsto (σ t : ℝ) (hσ : 0 < σ) :
    Tendsto (fun Y : ℕ ↦ RealEulerDamping.product (Nat.primesBelow Y) (fun _ ↦ 1) σ t)
      atTop (nhds (riemannZeta (ActualZetaTail.argument σ t))) := by
  have hZ := riemannZeta_eulerProduct (s := ActualZetaTail.argument σ t)
    (by rw [ActualZetaTail.argument_re]; linarith only [hσ])
  have he : (fun Y : ℕ ↦ RealEulerDamping.product (Nat.primesBelow Y) (fun _ ↦ 1) σ t)=
      (fun Y : ℕ ↦ ∏ p ∈ Nat.primesBelow Y, (1-(p : ℂ)^(-(ActualZetaTail.argument σ t)))⁻¹) := by
    funext Y
    rw [DampedFiniteEulerExtension.unit_product_as_integrand]
    unfold FiniteEulerLogBound.product
    apply prod_congr rfl
    intro p hp
    dsimp only
    rw [ActualZetaTail.nat_integrand_eq_cpow σ t hσ p,Complex.cpow_neg,one_div]
  rw [he]
  exact hZ

theorem fourth_power_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1) (σ t : ℝ) (hσ : 0 < σ) :
    ‖RealEulerDamping.product P f σ t‖^4 ≤
      Real.exp 8*‖riemannZeta (ActualZetaTail.argument σ 0)‖^3*
        ‖riemannZeta (ActualZetaTail.argument σ (2*t))‖ := by
  have hB := (unit_product_tendsto σ 0 hσ).norm.pow 3
  have hC := (unit_product_tendsto σ (2*t) hσ).norm
  apply ge_of_tendsto ((hB.const_mul (Real.exp 8)).mul hC)
  filter_upwards [eventually_ge_atTop (P.sup id+1)] with Y hY
  have hPQ : P ⊆ Nat.primesBelow Y := by
    intro p hp
    apply Nat.mem_primesBelow.mpr
    have hSup : p ≤ P.sup id := le_sup (f := id) hp
    exact ⟨by omega,hP p hp⟩
  exact DampedFiniteEulerExtension.enlarged_fourth_power_bound P (Nat.primesBelow Y) hPQ
    (fun p hp ↦ (Nat.mem_primesBelow.mp hp).2) f hf σ t hσ.le
end PaperP1.DampedEulerZetaComparison
