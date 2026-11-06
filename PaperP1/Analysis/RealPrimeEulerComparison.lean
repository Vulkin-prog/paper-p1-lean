module

public import PaperP1.Analysis.RealPrimeEulerBound
public import PaperP1.Analysis.RealUnitEulerComparison

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.RealPrimeEulerComparison
open Finset PaperP1 LogarithmicPhase
open scoped Classical

theorem phase_double (w t : ℝ) : phase w (2*t)=(phase w t)^2 := by
  unfold phase
  rw [pow_two,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem term_as_weight (f : ℕ → ℝ) (p : ℕ) (t : ℝ) :
    RealPrimeEulerBound.primeTerm f p t=
      (f p : ℂ)*((1/(p : ℝ) : ℝ) : ℂ)*phase (-Real.log p) t := by
  unfold RealPrimeEulerBound.primeTerm
  push_cast
  ring

theorem fourth_power_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1) (t : ℝ) :
    ‖RealPrimeEulerBound.product P f t‖^4 ≤
      Real.exp (8*(∑ p ∈ P, 1/(p : ℝ)^2))*
        ‖RealPrimeEulerBound.product P (fun _ ↦ 1) 0‖^3*
        ‖RealPrimeEulerBound.product P (fun _ ↦ 1) (2*t)‖ := by
  have hWeight : ∀ p ∈ P, 0 ≤ 1/(p : ℝ) ∧ 1/(p : ℝ) ≤ 1/2 := by
    intro p hp
    constructor
    · positivity
    · exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (hP p hp).two_le)
  have hh := RealUnitEulerComparison.fourth_power_bound P f (fun p ↦ 1/(p : ℝ))
    (fun p ↦ phase (-Real.log p) t) hf hWeight (fun p _ ↦ phase_norm _ _)
  have hA : (fun p ↦ (f p : ℂ)*((1/(p : ℝ) : ℝ) : ℂ)*phase (-Real.log p) t)=
      (fun p ↦ RealPrimeEulerBound.primeTerm f p t) := by
    funext p
    exact (term_as_weight f p t).symm
  have hB : (fun p : ℕ ↦ ((1/(p : ℝ) : ℝ) : ℂ))=
      (fun p ↦ RealPrimeEulerBound.primeTerm (fun _ ↦ 1) p 0) := by
    funext p
    simp [RealPrimeEulerBound.primeTerm,phase]
  have hC : (fun p : ℕ ↦ ((1/(p : ℝ) : ℝ) : ℂ)*(phase (-Real.log p) t)^2)=
      (fun p ↦ RealPrimeEulerBound.primeTerm (fun _ ↦ 1) p (2*t)) := by
    funext p
    rw [term_as_weight,phase_double]
    simp
  have hE : (∑ p ∈ P, (1/(p : ℝ))^2)=∑ p ∈ P, 1/(p : ℝ)^2 := by
    apply sum_congr rfl
    intro p hp
    ring
  rw [hA,hB,hC,hE] at hh
  exact hh
end PaperP1.RealPrimeEulerComparison
