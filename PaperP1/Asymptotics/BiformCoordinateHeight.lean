module

public import PaperP1.Diophantine.BiformCoordinateEquation

/-! # One transformed coefficient exponent before all moving lattice matrices -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiformCoordinateHeight

open PaperP1.BiformCoordinateEquation PaperP1.BiformLinearCoordinates

theorem explicit_bound_le_power (Amax Bmax a b κ μ ν N : ℕ)
    (ha : a ≤ Amax) (hb : b ≤ Bmax) (hN : 2 ≤ N)
    (hA : Amax + 1 ≤ N) (hB : Bmax + 1 ≤ N) :
    (b + 1) * ((a + 1) * N ^ κ * (2 * N ^ μ) ^ a) * (2 * N ^ ν) ^ b ≤
      N ^ (κ + (μ + 1) * Amax + (ν + 1) * Bmax + 2) := by
  have hμ : 2 * N ^ μ ≤ N ^ (μ + 1) := by
    rw [pow_succ']
    exact Nat.mul_le_mul_right _ hN
  have hν : 2 * N ^ ν ≤ N ^ (ν + 1) := by
    rw [pow_succ']
    exact Nat.mul_le_mul_right _ hN
  calc
    _ ≤ N * (N * N ^ κ * (N ^ (μ + 1)) ^ a) * (N ^ (ν + 1)) ^ b := by
      gcongr
      · omega
      · omega
    _ = N ^ (κ + (μ + 1) * a + (ν + 1) * b + 2) := by
      simp only [pow_add, pow_mul, pow_succ]
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega)
      (by gcongr)

theorem uniform_transformed_height (Amax Bmax κ μ ν : ℕ) :
    ∃ κ' N₀ : ℕ, ∀ N ≥ N₀, ∀ a ≤ Amax, ∀ b ≤ Bmax,
      ∀ A B : Matrix (Fin 2) (Fin 2) ℤ,
      ∀ F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ,
      (∀ i, (F i).IsHomogeneous b) →
      (∀ i m, ((F i).coeff m).natAbs ≤ N ^ κ) →
      (∀ i j, (A i j).natAbs ≤ N ^ μ) → (∀ i j, (B i j).natAbs ≤ N ^ ν) →
      ∀ m n, |((equation (b := b) (transform (b := b) A B F)).coeff m).coeff n| ≤ ((N ^ κ' : ℕ) : ℤ) := by
  refine ⟨κ + (μ + 1) * Amax + (ν + 1) * Bmax + 2,
    max 2 (max (Amax + 1) (Bmax + 1)), ?_⟩
  intro N hN a ha b hb A B F hF hH hM hT m n
  exact (transformed_equation_height A B F hF (N ^ κ) (N ^ μ) (N ^ ν) hH hM hT m n).trans
    (by exact_mod_cast (explicit_bound_le_power Amax Bmax a b κ μ ν N ha hb
      (by omega) (by omega) (by omega)))

end PaperP1.BiformCoordinateHeight
