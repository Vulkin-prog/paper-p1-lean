module

public import PaperP1.Arithmetic.ShortIntervalCongruences
public import Mathlib.Tactic.Ring

/-! # Counting centers with fixed integer offsets and coprime divisors

Only uniqueness of the common residue is needed; no choice of a CRT solution
or positivity assumption on the integer offsets enters these bounds.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerOffsetCRT

open Finset

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem common_modEq (q : ι → ℕ) (w : ι → ℤ) (x y : ℕ)
    (hx : ∀ j, (q j : ℤ) ∣ (x : ℤ) + w j)
    (hy : ∀ j, (q j : ℤ) ∣ (y : ℤ) + w j) :
    ∀ j, Nat.ModEq (q j) x y := by
  intro j
  apply Nat.modEq_iff_dvd.mpr
  have h := dvd_sub (hy j) (hx j)
  convert h using 1
  ring

theorem coordinate_card (S : Finset ℕ) (U N : ℕ) (q : ι → ℕ) (w : ι → ℤ)
    (hcop : Pairwise (fun i j ↦ Nat.Coprime (q i) (q j)))
    (hbox : S ⊆ Ico U (U + N))
    (hdiv : ∀ x ∈ S, ∀ j, (q j : ℤ) ∣ (x : ℤ) + w j) :
    S.card ≤ N / (∏ j, q j) + 1 := by
  apply ShortIntervalCongruences.card_common_residue_le S U N _ hbox
  intro x hx y hy
  exact ShortIntervalCongruences.product_dvd_difference q hcop x y
    (common_modEq q w x y (hdiv x hx) (hdiv y hy))

theorem box_card (d : ℕ) (F : Finset (Fin d → ℕ)) (U : Fin d → ℕ) (N : ℕ)
    (q : ι → ℕ) (w : ι → Fin d → ℤ)
    (hcop : Pairwise (fun i j ↦ Nat.Coprime (q i) (q j)))
    (hbox : ∀ X ∈ F, ∀ i, X i ∈ Ico (U i) (U i + N))
    (hdiv : ∀ X ∈ F, ∀ j i, (q j : ℤ) ∣ (X i : ℤ) + w j i) :
    F.card ≤ (N / (∏ j, q j) + 1) ^ d := by
  let S (i : Fin d) : Finset ℕ := F.image (fun X ↦ X i)
  have hcoord (i : Fin d) : (S i).card ≤ N / (∏ j, q j) + 1 := by
    apply coordinate_card (S i) (U i) N q (fun j ↦ w j i) hcop
    · intro x hx
      obtain ⟨X, hX, rfl⟩ := mem_image.mp hx
      exact hbox X hX i
    · intro x hx j
      obtain ⟨X, hX, rfl⟩ := mem_image.mp hx
      exact hdiv X hX j i
  have hsub : F ⊆ Fintype.piFinset S := by
    intro X hX
    exact Fintype.mem_piFinset.mpr (fun i ↦ mem_image_of_mem _ hX)
  calc
    F.card ≤ (Fintype.piFinset S).card := card_le_card hsub
    _ = ∏ i, (S i).card := Fintype.card_piFinset S
    _ ≤ ∏ _ : Fin d, (N / (∏ j, q j) + 1) := prod_le_prod (fun i _ ↦ hcoord i)
    _ = _ := by simp

end PaperP1.IntegerOffsetCRT
