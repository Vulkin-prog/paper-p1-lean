module

public import PaperP1.Analysis.RealPrimeEulerBound
public import PaperP1.Analysis.RealPrimeEulerComparison
public import PaperP1.Analysis.FiniteEulerDampingComparison
public import PaperP1.Analysis.PrimeDampingBudget

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.RealEulerDamping
open Finset PaperP1 LogarithmicPhase
open scoped Classical

def product (P : Finset ℕ) (f : ℕ → ℝ) (σ t : ℝ) : ℂ :=
  RealPrimeEulerBound.product P (fun p ↦ f p*(p : ℝ)^(-σ)) t

def constant : ℝ := Real.exp (Real.log 4+7)

theorem constant_pos : 0 < constant := Real.exp_pos _

theorem damped_coefficient_bound (f : ℕ → ℝ) (p : ℕ) (hp : p.Prime)
    (hf : |f p| ≤ 1) (σ : ℝ) (hσ : 0 ≤ σ) : |f p*(p : ℝ)^(-σ)| ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hD := PrimeDampingBudget.damping_bounds p σ hp1 hσ
  rw [abs_mul,abs_of_nonneg hD.1]
  exact (mul_le_mul_of_nonneg_right hf hD.1).trans (by simpa only [one_mul] using hD.2)

theorem norm_comparison (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ X) (f : ℕ → ℝ) (hf : ∀ p ∈ P, |f p| ≤ 1)
    (σ t : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hLog : σ*Real.log (X : ℝ) ≤ 1) :
    ‖RealPrimeEulerBound.product P f t‖ ≤ constant*‖product P f σ t‖ := by
  have hWeights : ∀ p ∈ P, 0 ≤ (p : ℝ)^(-σ)/(p : ℝ) ∧
      (p : ℝ)^(-σ)/(p : ℝ) ≤ 1/(p : ℝ) ∧ 1/(p : ℝ) ≤ 1/2 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).1.one_le
    have hD := PrimeDampingBudget.damping_bounds p σ hp1 hσ0
    exact ⟨div_nonneg hD.1 (Nat.cast_nonneg p),
      div_le_div_of_nonneg_right hD.2 (Nat.cast_nonneg p),
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (hP p hp).1.two_le)⟩
  have hh := FiniteEulerDampingComparison.norm_product_comparison P f
    (fun p ↦ 1/(p : ℝ)) (fun p ↦ (p : ℝ)^(-σ)/(p : ℝ))
    (fun p ↦ phase (-Real.log p) t) hf hWeights (fun p _ ↦ phase_norm _ _)
  have hA : (fun p ↦ (f p : ℂ)*((1/(p : ℝ) : ℝ) : ℂ)*phase (-Real.log p) t)=
      (fun p ↦ RealPrimeEulerBound.primeTerm f p t) := by
    funext p
    exact (RealPrimeEulerComparison.term_as_weight f p t).symm
  have hB : (fun p ↦ (f p : ℂ)*(((p : ℝ)^(-σ)/(p : ℝ) : ℝ) : ℂ)*phase (-Real.log p) t)=
      (fun p ↦ RealPrimeEulerBound.primeTerm (fun p ↦ f p*(p : ℝ)^(-σ)) p t) := by
    funext p
    rw [RealPrimeEulerComparison.term_as_weight]
    push_cast
    ring
  have hE : (∑ p ∈ P, (1/(p : ℝ))^2)=∑ p ∈ P, 1/(p : ℝ)^2 := by
    apply sum_congr rfl
    intro p hp
    ring
  rw [hA,hB,hE] at hh
  have hDefect := PrimeDampingBudget.uniform_summed_defect X hX P hP σ hσ0 hσ1 hLog
  have hSquare := PrimeDampingBudget.reciprocal_square_budget P (fun p hp ↦ (hP p hp).1)
  have hExp : Real.exp ((∑ p ∈ P, (1/(p : ℝ)-(p : ℝ)^(-σ)/(p : ℝ)))+
      2*(∑ p ∈ P, 1/(p : ℝ)^2)) ≤ constant := by
    apply Real.exp_le_exp.mpr
    linarith only [hDefect,hSquare]
  exact hh.trans (mul_le_mul_of_nonneg_right hExp (norm_nonneg _))

theorem logarithmic_norm_comparison (X : ℕ) (hX : 1 ≤ X) (hLog : 1 ≤ Real.log (X : ℝ))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≤ X) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1) (t : ℝ) :
    ‖RealPrimeEulerBound.product P f t‖ ≤ constant*‖product P f (1/Real.log (X : ℝ)) t‖ := by
  have hLP : 0 < Real.log (X : ℝ) := by linarith only [hLog]
  apply norm_comparison X hX P hP f hf _ t (by positivity)
  · have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hLog
    simpa only [div_one] using hh
  · have he : (1/Real.log (X : ℝ))*Real.log (X : ℝ)=1 := by field_simp
    exact he.le
end PaperP1.RealEulerDamping
