module

public import PaperP1.Analysis.PrimeLogFrequencyRows
public import PaperP1.Analysis.WeightedGaussianKernel

/-! # An actual uniform weighted-prime polynomial mean with a single logarithmic weight -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedPrimeMean
open Finset Nat MeasureTheory PaperP1 GaussianExponentialSums
open scoped Classical

def constant : ℝ := 400*Real.exp 1*Real.sqrt Real.pi*(1+2*Real.sqrt Real.pi)

def value (P : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  polynomial P (fun p ↦ ((Real.log (p : ℝ)/(p : ℝ) : ℝ) : ℂ)*a p)
    (fun p ↦ -Real.log (p : ℝ)) t

theorem constant_pos : 0 < constant := by dsimp only [constant]; positivity

theorem value_continuous (P : Finset ℕ) (a : ℕ → ℂ) : Continuous (value P a) :=
  polynomial_continuous _ _ _

theorem mean_square (P : Finset ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : 1 ≤ T)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ T^2 ≤ (p : ℝ)) :
    (∫ t in -T..T, ‖value P a t‖^2) ≤
      constant*∑ p ∈ P, (Real.log (p : ℝ)/(p : ℝ))*‖a p‖^2 := by
  let b : ℝ := 1/T^2
  let m : ℕ → ℝ := fun p ↦ Real.log (p : ℝ)/(p : ℝ)
  let w : ℕ → ℝ := fun p ↦ -Real.log (p : ℝ)
  let L : ℝ := (400/T)*(1+2*Real.sqrt Real.pi)
  have hTpos : 0 < T := by linarith
  have hb : 0 < b := by dsimp only [b]; positivity
  have hm : ∀ p ∈ P, 0 ≤ m p := by
    intro p hp
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).1.one_le)) (Nat.cast_nonneg p)
  have hrow : ∀ p ∈ P, (∑ q ∈ P, m q*Real.exp (-((w p-w q)^2/(4*b)))) ≤ L := by
    intro p hp
    have hh := PrimeLogFrequencyRows.gaussian_row P T (Real.log (p : ℝ)) hT hP
    convert hh using 1
    apply sum_congr rfl
    intro q hq
    congr 2
    dsimp only [w,b]
    field_simp
    ring
  have hg := WeightedGaussianKernel.gaussian_weighted_mean P a m w b L hb hm hrow
  have hl := interval_le_gaussian P (fun p ↦ (m p : ℂ)*a p) w b T hb hTpos
  have hbT : b*T^2=1 := by dsimp only [b]; field_simp
  rw [hbT] at hl
  have hroot : Real.sqrt (Real.pi/b)=Real.sqrt Real.pi*T := by
    have he : Real.pi/b=Real.pi*T^2 := by dsimp only [b]; field_simp
    rw [he,Real.sqrt_mul Real.pi_pos.le,Real.sqrt_sq hTpos.le]
  have he : Real.exp 1*(Real.sqrt (Real.pi/b)*L)=constant := by
    rw [hroot]
    dsimp only [L,constant]
    field_simp
  have hh := hl.trans (mul_le_mul_of_nonneg_left hg (Real.exp_pos 1).le)
  rw [← mul_assoc,he] at hh
  exact hh
end PaperP1.WeightedPrimeMean
