module

public import PaperP1.Arithmetic.PrivateEvenIntersection
public import PaperP1.Arithmetic.NormalizedWindowSets

/-! # Every actual set of bounded width lies in one complete original window, with an injective shifted center -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedWidthWindows

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets

local instance boundedWidthWindowsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def center (X R : ℕ) : ℕ := X - R + 1

theorem values_subset (U : Finset ℕ) (X R : ℕ) (hRX : R ≤ X)
    (hwidth : ∀ n ∈ U, ((n : ℤ) - X).natAbs ≤ R) :
    U ⊆ values (center X R) (2 * R) := by
  rw [values_eq_interval (by unfold center; omega)]
  intro n hn
  have hnat := hwidth n hn
  have habs : |(n : ℤ) - X| ≤ (R : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hnat
  have h := abs_le.mp habs
  have hcancel := Nat.sub_add_cancel hRX
  apply mem_Ico.mpr
  unfold center
  omega

theorem space_le_window (U : Finset ℕ) (X R : ℕ) (hRX : R ≤ X)
    (hwidth : ∀ n ∈ U, ((n : ℤ) - X).natAbs ≤ R) :
    FiniteEvenSquareClasses.space U ≤ squareClassSpace (center X R) (2 * R) := by
  rw [← space_values]
  exact PrivateEvenIntersection.space_mono (values_subset U X R hRX hwidth)

theorem window_space_mono {x L H : ℕ} (hx : 0 < x) (hLH : L ≤ H) :
    squareClassSpace x L ≤ squareClassSpace x H := by
  rw [← space_values, ← space_values]
  apply PrivateEvenIntersection.space_mono
  rw [values_eq_interval hx, values_eq_interval hx]
  intro n hn
  have h := mem_Ico.mp hn
  exact mem_Ico.mpr ⟨h.1, lt_of_lt_of_le h.2 (Nat.add_le_add_left hLH x)⟩

theorem center_injective_on (R : ℕ) (S : Finset ℕ) (hS : ∀ X ∈ S, R ≤ X) :
    Set.InjOn (fun X ↦ center X R) (S : Set ℕ) := by
  intro X hX Y hY hXY
  have hx := Nat.sub_add_cancel (hS X hX)
  have hy := Nat.sub_add_cancel (hS Y hY)
  change X - R + 1 = Y - R + 1 at hXY
  omega

end PaperP1.BoundedWidthWindows
