module

public import PaperP1.Model.WindowFamilyConditional
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The actual conditional sum splits at a large effective nullity increment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WindowConditionalSum

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.WindowFamilyConditional

local instance windowConditionalSumTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem finite_bound {s M N L : ℕ} (x : Fin s → ℕ) (a : SampleSpace M) (c : ℕ → Fin L → F₂)
    (hcut : ∀ i, x i + L ≤ M) (hM : 2 * N + L ≤ M)
    (hrel : ∀ z ∈ Ico N (2 * N),
      Module.finrank F₂ (WindowRelationCode.windowRelationCode (z - 1) (L + 1)) ≤ 1)
    (η : ℝ) :
    (∑ z ∈ Ico N (2 * N), conditionalProbability x L (fun i ↦ startSystem M (x i) L a) z (c z)) ≤
      (N : ℝ) * (2 * (2 ^ L : ℝ)⁻¹) * (2 : ℝ) ^ (η * L) +
        ((DenseTargetCover.targets x L N η).card : ℝ) := by
  classical
  let B : ℝ := 2 * (2 ^ L : ℝ)⁻¹ * (2 : ℝ) ^ (η * L)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (z : ℕ) (hz : z ∈ Ico N (2 * N)) :
      conditionalProbability x L (fun i ↦ startSystem M (x i) L a) z (c z) ≤
        B + if z ∈ DenseTargetCover.targets x L N η then 1 else 0 := by
    have hzb := mem_Ico.mp hz
    have hzM : z + L ≤ M := by omega
    have hzpos : 0 < z := by omega
    by_cases hlarge : z ∈ DenseTargetCover.targets x L N η
    · simp only [hlarge, ite_true]
      exact (conditional_le_one x a (c z) hcut hzM).trans (by linarith only [hB])
    · simp only [hlarge, ite_false, add_zero]
      have hsmall : (DenseTargetRegularization.loss (DenseTargetCover.extended x z) L : ℝ) < η * L := by
        exact lt_of_not_ge fun h ↦ hlarge ((DenseTargetCover.mem_targets x L N z η).mpr ⟨hz, h⟩)
      have hpow : (2 ^ DenseTargetRegularization.loss (DenseTargetCover.extended x z) L : ℝ) ≤
          (2 : ℝ) ^ (η * L) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hsmall.le
      calc
        _ ≤ 2 * (2 ^ DenseTargetRegularization.loss (DenseTargetCover.extended x z) L : ℝ) / (2 ^ L : ℝ) :=
          conditional_le_nominal x a (c z) hcut hzM hzpos (hrel z hz)
        _ ≤ 2 * (2 : ℝ) ^ (η * L) / (2 ^ L : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by positivity)
        _ = B := by dsimp [B]; rw [div_eq_mul_inv]; ring
  have hcard : (∑ z ∈ Ico N (2 * N), if z ∈ DenseTargetCover.targets x L N η then (1 : ℝ) else 0) =
      (DenseTargetCover.targets x L N η).card := by
    rw [← sum_filter]
    have heq : (Ico N (2 * N)).filter (fun z ↦ z ∈ DenseTargetCover.targets x L N η) =
        DenseTargetCover.targets x L N η := by
      ext z
      constructor
      · exact fun hz ↦ (mem_filter.mp hz).2
      · intro hz
        exact mem_filter.mpr ⟨((DenseTargetCover.mem_targets x L N z η).mp hz).1, hz⟩
    rw [heq]
    simp
  have hsum := sum_le_sum hpoint
  have hsize : (Ico N (2 * N)).card = N := by simp [two_mul]
  rw [sum_add_distrib, hcard, sum_const, nsmul_eq_mul, hsize] at hsum
  dsimp [B] at hsum
  simpa only [mul_assoc] using hsum

end PaperP1.WindowConditionalSum
