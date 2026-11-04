module

public import PaperP1.Probability.PositionalDeterministicMap

/-! # A literal uniform mixture of finitely many full configurations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalUniformAtoms

open Finset PaperP1.PositionalFiniteLaw PaperP1.FiniteConvolutionAlgebra
  PaperP1.CompletedPositionalLaw PaperP1.PositionalTotalMass PaperP1.PositivePositionalConvolution

variable {ι α : Type*}

def average (S : Finset α) (f : α → Configuration ι) : Space ι :=
  ((S.card : ℝ)⁻¹) • ∑ a ∈ S, ofFinite (atom (f a))

theorem average_isProbability (S : Finset α) (hS : S.Nonempty) (f : α → Configuration ι) :
    IsProbability (average S f) := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hS).ne'
  constructor
  · intro v
    rw [average, map_smul, map_sum, smul_eq_mul]
    exact mul_nonneg (by positivity) (sum_nonneg fun a _ ↦
      (PositionalDeterministicMap.atom_isProbability (f a)).1 v)
  · rw [average, map_smul, map_sum, smul_eq_mul]
    simp only [totalMass_ofFinite, mass_atom, sum_const, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hcard

theorem hasSum_test (S : Finset α) (f : α → Configuration ι) (g : Configuration ι → ℝ) :
    HasSum (fun v ↦ coeff v (average S f) * g v)
      ((S.card : ℝ)⁻¹ * ∑ a ∈ S, g (f a)) := by
  have hs := (hasSum_sum (s := S) (fun a _ ↦
    PositionalDeterministicMap.hasSum_atom_test (f a) g)).mul_left ((S.card : ℝ)⁻¹)
  convert hs using 1
  funext v
  simp only [average, map_smul, map_sum, smul_eq_mul, mul_sum, sum_mul, mul_assoc]

theorem test_bound (S : Finset α) (hS : S.Nonempty) (f : α → Configuration ι)
    (g : Configuration ι → ℝ) (B : ℝ) (hB : ∀ a ∈ S, g (f a) ≤ B) :
    (∑' v, coeff v (average S f) * g v) ≤ B := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hS).ne'
  rw [(hasSum_test S f g).tsum_eq]
  calc
    _ ≤ (S.card : ℝ)⁻¹ * ∑ _a ∈ S, B := mul_le_mul_of_nonneg_left
      (sum_le_sum hB) (by positivity)
    _ = B := by rw [sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end PaperP1.PositionalUniformAtoms
