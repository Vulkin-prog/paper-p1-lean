module

public import PaperP1.Analysis.RealPrimeEulerComparison
public import PaperP1.Analysis.DampedLogarithmicIntegral
public import PaperP1.Analysis.PrimeDampingBudget
public import PaperP1.Analysis.RealEulerDamping
public import PaperP1.Analysis.RealUnitEulerComparison

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.DampedFiniteEulerExtension
open Finset PaperP1 LogarithmicPhase
open scoped Classical

def weight (σ : ℝ) (p : ℕ) : ℝ := (p : ℝ)^(-σ)/(p : ℝ)

theorem product_as_finite (P : Finset ℕ) (f : ℕ → ℝ) (σ t : ℝ) :
    RealEulerDamping.product P f σ t=
      FiniteEulerLogBound.product P (fun p ↦ (f p : ℂ)*(weight σ p : ℂ)*phase (-Real.log p) t) := by
  unfold RealEulerDamping.product RealPrimeEulerBound.product
  congr 1
  funext p
  unfold RealPrimeEulerBound.primeTerm weight
  push_cast
  ring

theorem unit_product_as_integrand (P : Finset ℕ) (σ t : ℝ) :
    RealEulerDamping.product P (fun _ ↦ 1) σ t=
      FiniteEulerLogBound.product P (fun p ↦ DampedLogarithmicIntegral.integrand σ t p) := by
  rw [product_as_finite]
  congr 1
  funext p
  unfold DampedLogarithmicIntegral.integrand DampedLogarithmicIntegral.numerator
    LogarithmicExponentialSum.function weight
  push_cast
  ring

theorem extend_zero (P Q : Finset ℕ) (hPQ : P ⊆ Q) (f : ℕ → ℝ) (σ t : ℝ) :
    RealEulerDamping.product Q (fun p ↦ if p ∈ P then f p else 0) σ t=
      RealEulerDamping.product P f σ t := by
  rw [product_as_finite,product_as_finite]
  unfold FiniteEulerLogBound.product
  calc
    _ = ∏ p ∈ P, (1-(((if p ∈ P then f p else 0) : ℝ) : ℂ)*(weight σ p : ℂ)*phase (-Real.log p) t)⁻¹ := by
      apply (prod_subset hPQ _).symm
      intro p hpQ hpP
      simp [hpP]
    _ = _ := by
      apply prod_congr rfl
      intro p hp
      simp only [hp,ite_true]

theorem enlarged_fourth_power_bound (P Q : Finset ℕ) (hPQ : P ⊆ Q)
    (hQ : ∀ p ∈ Q, p.Prime) (f : ℕ → ℝ) (hf : ∀ p ∈ P, |f p| ≤ 1)
    (σ t : ℝ) (hσ : 0 ≤ σ) :
    ‖RealEulerDamping.product P f σ t‖^4 ≤
      Real.exp 8*‖RealEulerDamping.product Q (fun _ ↦ 1) σ 0‖^3*
        ‖RealEulerDamping.product Q (fun _ ↦ 1) σ (2*t)‖ := by
  let g := fun p ↦ if p ∈ P then f p else 0
  have hg : ∀ p ∈ Q, |g p| ≤ 1 := by
    intro p hp
    dsimp only [g]
    split_ifs with hh
    · exact hf p hh
    · norm_num
  have hWeight : ∀ p ∈ Q, 0 ≤ weight σ p ∧ weight σ p ≤ 1/(p : ℝ) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQ p hp).one_le
    have hD := PrimeDampingBudget.damping_bounds p σ hp1 hσ
    exact ⟨div_nonneg hD.1 (Nat.cast_nonneg p),div_le_div_of_nonneg_right hD.2 (Nat.cast_nonneg p)⟩
  have hHalf : ∀ p ∈ Q, 0 ≤ weight σ p ∧ weight σ p ≤ 1/2 := by
    intro p hp
    exact ⟨(hWeight p hp).1,(hWeight p hp).2.trans
      (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (hQ p hp).two_le))⟩
  have hh := RealUnitEulerComparison.fourth_power_bound Q g (weight σ)
    (fun p ↦ phase (-Real.log p) t) hg hHalf (fun p _ ↦ phase_norm _ _)
  have hA := product_as_finite Q g σ t
  rw [← hA,extend_zero P Q hPQ f σ t] at hh
  have hB : FiniteEulerLogBound.product Q (fun p ↦ (weight σ p : ℂ))=
      RealEulerDamping.product Q (fun _ ↦ 1) σ 0 := by
    rw [product_as_finite]
    simp [phase]
  have hC : FiniteEulerLogBound.product Q (fun p ↦ (weight σ p : ℂ)*(phase (-Real.log p) t)^2)=
      RealEulerDamping.product Q (fun _ ↦ 1) σ (2*t) := by
    rw [product_as_finite]
    congr 1
    funext p
    rw [RealPrimeEulerComparison.phase_double]
    simp
  rw [hB,hC] at hh
  have hE : (∑ p ∈ Q, (weight σ p)^2) ≤ 1 := by
    apply le_trans _ (PrimeDampingBudget.reciprocal_square_budget Q hQ)
    apply sum_le_sum
    intro p hp
    have hh := pow_le_pow_left₀ (hWeight p hp).1 (hWeight p hp).2 2
    simpa only [div_pow,one_pow] using hh
  have hExp := Real.exp_le_exp.mpr (show 8*(∑ p ∈ Q, (weight σ p)^2) ≤ 8 by linarith only [hE])
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hExp (by positivity)) (norm_nonneg _))
end PaperP1.DampedFiniteEulerExtension
