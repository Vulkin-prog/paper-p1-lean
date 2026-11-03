module

public import PaperP1.Diophantine.GridRationalGraphExclusion
public import PaperP1.Asymptotics.CriticalPolynomialScale

/-! # Uniform exclusion of the actual grid-determined rational graphs at large critical dyadic scales -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalGridGraphExclusion

open Polynomial PaperP1.SelectedProportionalPairs

def constant (a : ℕ) : ℕ :=
  let C := (3 * ((2 * a + 1) + 1)) ^ (2 * a + 1)
  C + (2 * a).factorial * C ^ (2 * a) + (a + 2) * C

def exponent (a : ℕ) : ℕ := ((a + 1) * (2 * a + 1)) * (2 * a)

theorem bound_le_power (a B : ℕ) (ha : 0 < a) (hB : 1 ≤ B) :
    GridRationalGraphExclusion.bound a B ≤ constant a * B ^ exponent a :=
  GridRationalGraphExclusion.bound_le_polynomial a B ha hB

theorem cutoff_lt_scale (C : ℝ) (a J : ℕ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
        GridRationalGraphExclusion.bound a B < N := by
  obtain ⟨N₀, hN₀⟩ := CriticalPolynomialScale.polynomial_lt_scale C (constant a : ℝ)
    (Nat.cast_nonneg _) (J * exponent a)
  refine ⟨N₀, fun N hN L B hcrit hB hBL ↦ ?_⟩
  have hs : constant a * (L + 1) ^ (J * exponent a) < N := by exact_mod_cast hN₀ N hN L hcrit
  calc
    GridRationalGraphExclusion.bound a B ≤ constant a * B ^ exponent a := bound_le_power a B ha hB
    _ ≤ constant a * ((L + 1) ^ J) ^ exponent a :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hBL _)
    _ = constant a * (L + 1) ^ (J * exponent a) :=
      congrArg (fun z ↦ constant a * z) (pow_mul (L + 1) J (exponent a)).symm
    _ < N := hs

theorem eventually_no_dyadic_point (C : ℝ) (a J : ℕ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ i j : Fin (2 * a + 1) → ℤ, Function.Injective i →
        (∀ t, (i t).natAbs ≤ B) → (∀ t, (j t).natAbs ≤ B) →
        ∀ S T : Finset ℤ, (∀ t, i t ∈ S) → (∀ t, j t ∈ T) →
        ∀ p q : ℚ[X], q ≠ 0 → IsCoprime p q → max p.natDegree q.natDegree = a →
          (∀ t, p.eval (-(i t : ℚ)) = -(j t : ℚ) * q.eval (-(i t : ℚ))) →
          ∀ X Y : ℤ, (N : ℤ) ≤ X → Y.natAbs ≤ 2 * N →
            p.eval (X : ℚ) = (Y : ℚ) * q.eval (X : ℚ) →
            (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
            EvenIndependentValues.Independent (values X S) →
            Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T)) →
            False := by
  obtain ⟨N₀, hN₀⟩ := cutoff_lt_scale C a J ha
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL i j hinj hiB hjB S T hiS hjT p q hq0 hcop hdegree hgrid X Y hXN hYN hpoint hposS hposT hind hdirect
  have hXNabs : N ≤ X.natAbs := by
    have hz : (N : ℤ) ≤ (X.natAbs : ℤ) := hXN.trans Int.le_natAbs
    exact_mod_cast hz
  have hsmall := GridRationalGraphExclusion.integral_point a B ha hB i j hinj hiB hjB S T hiS hjT p q
    hq0 hcop hdegree hgrid X Y (hYN.trans (Nat.mul_le_mul_left 2 hXNabs)) hpoint hposS hposT hind hdirect
  exact Nat.not_lt_of_ge hXNabs (hsmall.trans_lt (hN₀ N hN L B hcrit hB hBL))

end PaperP1.CriticalGridGraphExclusion
