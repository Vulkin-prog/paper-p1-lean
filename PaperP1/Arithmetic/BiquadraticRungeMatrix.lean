module

public import PaperP1.Algebra.BivariateRungeCoefficients
public import PaperP1.Arithmetic.BiquadraticAuxiliaryCoordinates

/-! # The actual finite Runge coefficient matrix has an explicit small integer kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticRungeMatrix

open Finset PaperP1.RungeCoefficients PaperP1.BivariateRungeCoefficients
  PaperP1.BiquadraticAuxiliaryBudget PaperP1.BiquadraticAuxiliaryCoordinates

def blockRank (r : Fin 3 → ℕ) : Fin 4 → ℕ := Fin.cases 0 r

def character {q : ℕ} {r s : Fin 3 → ℕ} : CoefficientIndex q r s → Fin 4
  | .inl _ => 0
  | .inr p => p.1.succ

def xDegree {q : ℕ} {r s : Fin 3 → ℕ} : CoefficientIndex q r s → ℕ
  | .inl p => p.1.val
  | .inr p => p.2.1.val

def yDegree {q : ℕ} {r s : Fin 3 → ℕ} : CoefficientIndex q r s → ℕ
  | .inl p => p.2.val
  | .inr p => p.2.2.val

def xShift {q : ℕ} {r s : Fin 3 → ℕ} (i : CoefficientIndex q r s) : ℕ :=
  3 * q - blockRank r (character i) - xDegree i

def yShift {q : ℕ} {r s : Fin 3 → ℕ} (i : CoefficientIndex q r s) : ℕ :=
  3 * q - blockRank s (character i) - yDegree i

theorem rank_bound (q : ℕ) (r : Fin 3 → ℕ) (hr : ∀ i, r i ≤ q) (χ : Fin 4) :
    blockRank r χ ≤ q := by
  refine Fin.cases ?_ ?_ χ
  · exact Nat.zero_le q
  · intro i
    exact hr i

theorem slot_degree_bound {q : ℕ} {r s : Fin 3 → ℕ} (i : CoefficientIndex q r s) :
    xDegree i ≤ 3 * q - blockRank r (character i) ∧
      yDegree i ≤ 3 * q - blockRank s (character i) := by
  rcases i with p | ⟨j, p⟩
  · change p.1.val ≤ 3 * q - 0 ∧ p.2.val ≤ 3 * q - 0
    have hx := p.1.isLt
    have hy := p.2.isLt
    omega
  · change p.1.val ≤ 3 * q - r j ∧ p.2.val ≤ 3 * q - s j
    have hx := p.1.isLt
    have hy := p.2.isLt
    omega

theorem shift_identity {q : ℕ} {r s : Fin 3 → ℕ} (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (i : CoefficientIndex q r s) :
    xShift i + xDegree i + blockRank r (character i) = 3 * q ∧
      yShift i + yDegree i + blockRank s (character i) = 3 * q := by
  have hx := (slot_degree_bound i).1
  have hy := (slot_degree_bound i).2
  have hr' := rank_bound q r hr (character i)
  have hs' := rank_bound q s hs (character i)
  constructor
  · unfold xShift
    omega
  · unfold yShift
    omega

theorem residual_degree {q : ℕ} {r s : Fin 3 → ℕ} (j : EquationIndex q) (i : CoefficientIndex q r s) :
    (j.1.val - xShift i) + (j.2.val - yShift i) ≤ 6 * q :=
  (Nat.add_le_add (Nat.sub_le _ _) (Nat.sub_le _ _)).trans (equation_total_degree q j)

def rationalEntry {q : ℕ} {r s : Fin 3 → ℕ}
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (j : EquationIndex q) (i : CoefficientIndex q r s) : ℚ :=
  if xShift i ≤ j.1.val ∧ yShift i ≤ j.2.val then
    rungeCoefficient (γ (character i)) (j.1.val - xShift i) *
      rungeCoefficient (δ (character i)) (j.2.val - yShift i) else 0

def integerEntry {q : ℕ} {r s : Fin 3 → ℕ}
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (j : EquationIndex q) (i : CoefficientIndex q r s) : ℤ :=
  if xShift i ≤ j.1.val ∧ yShift i ≤ j.2.val then
    scaledCoefficient (γ (character i)) (δ (character i)) (6 * q)
      (j.1.val - xShift i) (j.2.val - yShift i) (residual_degree j i) else 0

theorem integerEntry_spec {q : ℕ} {r s : Fin 3 → ℕ}
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (j : EquationIndex q) (i : CoefficientIndex q r s) :
    (integerEntry γ δ j i : ℚ) = (2 : ℚ) ^ (12 * q) * rationalEntry γ δ j i := by
  unfold integerEntry rationalEntry
  split_ifs
  · simpa only [show 2 * (6 * q) = 12 * q by omega] using scaledCoefficient_spec
      (γ (character i)) (δ (character i)) (6 * q) _ _ (residual_degree j i)
  · simp only [Int.cast_zero, mul_zero]

theorem integerEntry_height {q : ℕ} {r s : Fin 3 → ℕ} (B : ℕ) (hB : 1 ≤ B)
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (hγ : ∀ χ i, |γ χ i| ≤ (B : ℤ)) (hδ : ∀ χ i, |δ χ i| ≤ (B : ℤ))
    (j : EquationIndex q) (i : CoefficientIndex q r s) :
    |integerEntry γ δ j i| ≤ ((B + 1) ^ (28 * q) : ℕ) := by
  unfold integerEntry
  split_ifs
  · apply scaled_height _ _ B q _ _ hB (residual_degree j i)
    · have hri := rank_bound q r hr (character i)
      have hsi := rank_bound q s hs (character i)
      omega
    · exact hγ _
    · exact hδ _
  · simp only [abs_zero]
    positivity

theorem exists_coefficients {q : ℕ} {r s : Fin 3 → ℕ} (B : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (hγ : ∀ χ i, |γ χ i| ≤ (B : ℤ)) (hδ : ∀ χ i, |δ χ i| ≤ (B : ℤ)) :
    ∃ w : CoefficientIndex q r s → ℤ, w ≠ 0 ∧
      (∀ i, |w i| ≤ ((B + 1) ^ (266 * q) : ℕ)) ∧
        ∀ j : EquationIndex q, ∑ i, rationalEntry γ δ j i * (w i : ℚ) = 0 := by
  let H := (B + 1) ^ (28 * q)
  have hB : 1 ≤ B := hq.trans hqB
  obtain ⟨w, hne, hbound, hzero⟩ := indexed_kernel q r s hr hs H (by dsimp [H]; positivity)
    (integerEntry γ δ) (integerEntry_height B hB hr hs γ δ hγ hδ)
  have hheight : (3 * unknownCount q r s * H) ^ 7 ≤ (B + 1) ^ (266 * q) :=
    kernel_height B q 28 H hq hqB r s le_rfl
  refine ⟨w, hne, fun i ↦ (hbound i).trans (by exact_mod_cast hheight), ?_⟩
  intro j
  have h := congrArg (fun z : ℤ ↦ (z : ℚ)) (hzero j)
  push_cast at h
  simp_rw [integerEntry_spec] at h
  have hscaled : (2 : ℚ) ^ (12 * q) * (∑ i, rationalEntry γ δ j i * (w i : ℚ)) = 0 := by
    simpa only [mul_assoc, ← mul_sum] using h
  exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero _ (by norm_num))

end PaperP1.BiquadraticRungeMatrix
