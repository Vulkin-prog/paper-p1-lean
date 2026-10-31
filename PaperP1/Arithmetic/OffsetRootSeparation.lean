module

public import PaperP1.Arithmetic.TwoPointSquareClasses
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Common roots after a rational line substitution in two direct windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetRootSeparation

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.TwoPointSquareClasses

def offset {L : ℕ} (u : Fin (L + 1)) : ℚ := (u.val : ℚ) - 1

def leftRoot {L : ℕ} (u : Fin (L + 1)) : ℚ := -offset u

def rightRoot {L : ℕ} (α β : ℚ) (v : Fin (L + 1)) : ℚ := -(β + offset v) / α

def commonRoots (L : ℕ) (α β : ℚ) : Finset ℚ :=
  (univ.image (leftRoot (L := L))) ∩ (univ.image (rightRoot (L := L) α β))

theorem leftRoot_injective (L : ℕ) : Function.Injective (leftRoot (L := L)) := by
  intro u v h
  apply Fin.ext
  have hval : (u.val : ℚ) = v.val := by dsimp [leftRoot, offset] at h; linarith
  exact_mod_cast hval

theorem rightRoot_injective (L : ℕ) (α β : ℚ) (hα : α ≠ 0) :
    Function.Injective (rightRoot (L := L) α β) := by
  intro u v h
  apply Fin.ext
  have hmul := congrArg (fun r : ℚ ↦ r * α) h
  dsimp [rightRoot, offset] at hmul
  field_simp at hmul
  have hval : (u.val : ℚ) = v.val := by linarith
  exact_mod_cast hval

theorem vertex_cast_value (x L : ℕ) (hx : 2 ≤ x) (u : Fin (L + 1)) :
    (startCompleteVertexLabel x L u : ℚ) = (x : ℚ) + offset u := by
  rw [startCompleteVertexLabel_eq_offset (by omega), Nat.cast_add,
    Nat.cast_sub (by omega : 1 ≤ x), Nat.cast_one]
  unfold offset
  ring

theorem value_proportional_of_root_match (x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (α β : ℚ) (hα : α ≠ 0) (hline : (y : ℚ) = α * (x : ℚ) + β)
    (u v : Fin (L + 1)) (hroot : leftRoot u = rightRoot α β v) :
    (startCompleteVertexLabel y L v : ℚ) = α * (startCompleteVertexLabel x L u : ℚ) := by
  have hroot' : -offset u * α = -(β + offset v) := (eq_div_iff hα).mp hroot
  rw [vertex_cast_value x L hx, vertex_cast_value y L hy]
  nlinarith

/-- Only the first of the two windows needs an injective even-selection map. -/
theorem match_left_unique (x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hinj : Function.Injective (evenSquareClassMap x L))
    (hdirect : Disjoint (squareClassSpace x L) (squareClassSpace y L))
    (α β : ℚ) (hα : α ≠ 0) (hline : (y : ℚ) = α * (x : ℚ) + β)
    (u₁ v₁ u₂ v₂ : Fin (L + 1)) (hroot₁ : leftRoot u₁ = rightRoot α β v₁)
    (hroot₂ : leftRoot u₂ = rightRoot α β v₂) : u₁ = u₂ := by
  by_contra hu
  have h₁ := value_proportional_of_root_match x y L hx hy α β hα hline u₁ v₁ hroot₁
  have h₂ := value_proportional_of_root_match x y L hx hy α β hα hline u₂ v₂ hroot₂
  have hcrossRat :
      (startCompleteVertexLabel x L u₁ : ℚ) * (startCompleteVertexLabel y L v₂ : ℚ) =
      (startCompleteVertexLabel x L u₂ : ℚ) * (startCompleteVertexLabel y L v₁ : ℚ) := by
    rw [h₁, h₂]
    ring
  have hcross : startCompleteVertexLabel x L u₁ * startCompleteVertexLabel y L v₂ =
      startCompleteVertexLabel x L u₂ * startCompleteVertexLabel y L v₁ := by exact_mod_cast hcrossRat
  exact no_proportional_pairs x y L hx hy hinj hdirect u₁ u₂ v₁ v₂ hu hcross

theorem commonRoots_card_le_one (x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hinj : Function.Injective (evenSquareClassMap x L))
    (hdirect : Disjoint (squareClassSpace x L) (squareClassSpace y L))
    (α β : ℚ) (hα : α ≠ 0) (hline : (y : ℚ) = α * (x : ℚ) + β) :
    (commonRoots L α β).card ≤ 1 := by
  apply card_le_one.mpr
  intro r hr s hs
  obtain ⟨hrl, hrr⟩ := mem_inter.mp hr
  obtain ⟨hsl, hsr⟩ := mem_inter.mp hs
  obtain ⟨u₁, _, hu₁⟩ := mem_image.mp hrl
  obtain ⟨v₁, _, hv₁⟩ := mem_image.mp hrr
  obtain ⟨u₂, _, hu₂⟩ := mem_image.mp hsl
  obtain ⟨v₂, _, hv₂⟩ := mem_image.mp hsr
  have hu := match_left_unique x y L hx hy hinj hdirect α β hα hline u₁ v₁ u₂ v₂
    (hu₁.trans hv₁.symm) (hu₂.trans hv₂.symm)
  exact hu₁.symm.trans ((congrArg leftRoot hu).trans hu₂)

end PaperP1.OffsetRootSeparation
