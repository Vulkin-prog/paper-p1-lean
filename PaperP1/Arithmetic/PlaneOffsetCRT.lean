module

public import PaperP1.Arithmetic.IntegerOffsetCRT
public import PaperP1.Algebra.TripleCross

/-! # Two free residue coordinates on an actual integer plane -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneOffsetCRT

open Finset PaperP1.TripleCross

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem projection_injective (F : Finset (Fin 3 → ℕ)) (A : Fin 3 → ℤ) (h : ℤ)
    (hA : A 2 ≠ 0) (hplane : ∀ X ∈ F, dot A (fun i ↦ (X i : ℤ)) = h) :
    Set.InjOn (fun X : Fin 3 → ℕ ↦ (X 0, X 1)) F := by
  intro X hX Y hY heq
  have h0 : X 0 = Y 0 := congrArg Prod.fst heq
  have h1 : X 1 = Y 1 := congrArg Prod.snd heq
  have hx := hplane X hX
  have hy := hplane Y hY
  simp only [dot, h0, h1] at hx hy
  have hmul : A 2 * (X 2 : ℤ) = A 2 * (Y 2 : ℤ) := by linarith
  have h2 : X 2 = Y 2 := by exact_mod_cast (mul_left_cancel₀ hA hmul)
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem plane_card (F : Finset (Fin 3 → ℕ)) (U : Fin 3 → ℕ) (N : ℕ)
    (q : ι → ℕ) (w : ι → Fin 3 → ℤ)
    (hcop : Pairwise (fun i j ↦ Nat.Coprime (q i) (q j)))
    (hbox : ∀ X ∈ F, ∀ i, X i ∈ Ico (U i) (U i + N))
    (hdiv : ∀ X ∈ F, ∀ j i, (q j : ℤ) ∣ (X i : ℤ) + w j i)
    (A : Fin 3 → ℤ) (h : ℤ) (hA : A 2 ≠ 0)
    (hplane : ∀ X ∈ F, dot A (fun i ↦ (X i : ℤ)) = h) :
    F.card ≤ (N / (∏ j, q j) + 1) ^ 2 := by
  let S (i : Fin 3) : Finset ℕ := F.image (fun X ↦ X i)
  have hcoord (i : Fin 3) : (S i).card ≤ N / (∏ j, q j) + 1 := by
    apply IntegerOffsetCRT.coordinate_card (S i) (U i) N q (fun j ↦ w j i) hcop
    · intro x hx
      obtain ⟨X, hX, rfl⟩ := mem_image.mp hx
      exact hbox X hX i
    · intro x hx j
      obtain ⟨X, hX, rfl⟩ := mem_image.mp hx
      exact hdiv X hX j i
  have himage : F.image (fun X ↦ (X 0, X 1)) ⊆ (S 0) ×ˢ (S 1) := by
    intro p hp
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hp
    exact mem_product.mpr ⟨mem_image_of_mem _ hX, mem_image_of_mem _ hX⟩
  calc
    F.card = (F.image (fun X ↦ (X 0, X 1))).card :=
      (card_image_of_injOn (projection_injective F A h hA hplane)).symm
    _ ≤ ((S 0) ×ˢ (S 1)).card := card_le_card himage
    _ = (S 0).card * (S 1).card := card_product _ _
    _ ≤ (N / (∏ j, q j) + 1) * (N / (∏ j, q j) + 1) :=
      Nat.mul_le_mul (hcoord 0) (hcoord 1)
    _ = _ := (pow_two _).symm

end PaperP1.PlaneOffsetCRT
