module

public import PaperP1.Arithmetic.IntegerOffsetCRT
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-! # Only two congruence coordinates are needed on any genuine real affine plane -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FreePlaneCRT

open Finset

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem projection_injective (F : Finset (Fin 3 → ℕ)) (A : Fin 3 → ℝ) (h : ℝ)
    (k : Fin 3) (hA : A k ≠ 0)
    (hplane : ∀ X ∈ F, (∑ i, A i * (X i : ℝ)) = h) :
    Set.InjOn (fun X : Fin 3 → ℕ ↦ fun i : Fin 2 ↦ X (k.succAbove i)) F := by
  intro X hX Y hY heq
  have hx := hplane X hX
  have hy := hplane Y hY
  rw [Fin.sum_univ_succAbove (fun i ↦ A i * (X i : ℝ)) k] at hx
  rw [Fin.sum_univ_succAbove (fun i ↦ A i * (Y i : ℝ)) k] at hy
  have hsum : (∑ i : Fin 2, A (k.succAbove i) * (X (k.succAbove i) : ℝ)) =
      ∑ i : Fin 2, A (k.succAbove i) * (Y (k.succAbove i) : ℝ) := by
    apply sum_congr rfl
    intro i _
    have hi : X (k.succAbove i) = Y (k.succAbove i) := congrFun heq i
    rw [hi]
  have hmul : A k * (X k : ℝ) = A k * (Y k : ℝ) := by linarith
  have hk : X k = Y k := by exact_mod_cast mul_left_cancel₀ hA hmul
  funext i
  rcases Fin.eq_self_or_eq_succAbove k i with rfl | ⟨j, rfl⟩
  · exact hk
  · exact congrFun heq j

theorem card_bound (F : Finset (Fin 3 → ℕ)) (base : Fin 3 → ℕ) (width : ℕ)
    (q : ι → ℕ) (w : ι → Fin 2 → ℤ)
    (hcop : Pairwise (fun i j ↦ Nat.Coprime (q i) (q j)))
    (A : Fin 3 → ℝ) (h : ℝ) (k : Fin 3) (hA : A k ≠ 0)
    (hplane : ∀ X ∈ F, (∑ i, A i * (X i : ℝ)) = h)
    (hbox : ∀ X ∈ F, ∀ i, X i ∈ Ico (base i) (base i + width))
    (hdiv : ∀ X ∈ F, ∀ j i, (q j : ℤ) ∣ (X (k.succAbove i) : ℤ) + w j i) :
    F.card ≤ (width / (∏ j, q j) + 1) ^ 2 := by
  let project (X : Fin 3 → ℕ) : Fin 2 → ℕ := fun i ↦ X (k.succAbove i)
  let G := F.image project
  have hcard : F.card = G.card := (card_image_of_injOn (projection_injective F A h k hA hplane)).symm
  rw [hcard]
  apply IntegerOffsetCRT.box_card 2 G (fun i ↦ base (k.succAbove i)) width q w hcop
  · intro Y hY i
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hY
    exact hbox X hX (k.succAbove i)
  · intro Y hY j i
    obtain ⟨X, hX, rfl⟩ := mem_image.mp hY
    exact hdiv X hX j i

theorem card_real_bound (F : Finset (Fin 3 → ℕ)) (base : Fin 3 → ℕ) (width : ℕ)
    (q : ι → ℕ) (w : ι → Fin 2 → ℤ)
    (hcop : Pairwise (fun i j ↦ Nat.Coprime (q i) (q j)))
    (A : Fin 3 → ℝ) (h : ℝ) (k : Fin 3) (hA : A k ≠ 0)
    (hplane : ∀ X ∈ F, (∑ i, A i * (X i : ℝ)) = h)
    (hbox : ∀ X ∈ F, ∀ i, X i ∈ Ico (base i) (base i + width))
    (hdiv : ∀ X ∈ F, ∀ j i, (q j : ℤ) ∣ (X (k.succAbove i) : ℤ) + w j i) :
    (F.card : ℝ) ≤ ((width : ℝ) / (∏ j, q j : ℕ) + 1) ^ 2 := by
  calc
    _ ≤ ((width / (∏ j, q j) + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast card_bound F base width q w hcop A h k hA hplane hbox hdiv
    _ ≤ _ := by
      apply pow_le_pow_left₀ (by positivity)
      rw [Nat.cast_add, Nat.cast_one]
      exact add_le_add Nat.cast_div_le le_rfl

end PaperP1.FreePlaneCRT
