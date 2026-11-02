module

public import PaperP1.Arithmetic.CompressedTargetAlignment
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Actual aligned targets have a polynomial bound in the window width

The source base and the ambient finite population are arbitrary. Bounded
positive affine slopes and a bounded integer remainder give the finite count.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedTargetCount

open Finset PaperP1.CompressedTargetAlignment

local instance alignedTargetCountDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def radius (D L : ℕ) : ℕ := 2 * D * (L + 1) ^ 4

def codes (L : ℕ) : Finset ℕ := Icc 1 ((L + 1) ^ 3)

def band (G : Finset ℕ) (X r s R : ℕ) : Finset ℕ :=
  G.filter fun z ↦ |(r : ℤ) * z - (s : ℤ) * X| ≤ R

def targets (G : Finset ℕ) (D X L : ℕ) : Finset ℕ :=
  G.filter fun z ↦ Aligned D X z L

theorem codes_card (L : ℕ) : (codes L).card = (L + 1) ^ 3 := by simp [codes]

theorem band_card (G : Finset ℕ) (X r s R : ℕ) (hr : 0 < r) :
    (band G X r s R).card ≤ 2 * R + 1 := by
  have hcard : (Icc (-(R : ℤ)) (R : ℤ)).card = 2 * R + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ (Icc (-(R : ℤ)) (R : ℤ)).card := by
      apply card_le_card_of_injOn (fun z : ℕ ↦ (r : ℤ) * z - (s : ℤ) * X)
      · intro z hz
        exact mem_Icc.mpr (abs_le.mp (mem_filter.mp hz).2)
      · intro z _ w _ heq
        have hrZ : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
        have hmul : (r : ℤ) * z = (r : ℤ) * w := by linarith only [heq]
        exact_mod_cast mul_left_cancel₀ hrZ hmul
    _ = _ := hcard

theorem target_cover (G : Finset ℕ) (D X L : ℕ) :
    targets G D X L ⊆ (codes L).biUnion
      (fun r ↦ (codes L).biUnion fun s ↦ band G X r s (radius D L)) := by
  intro z hz
  obtain ⟨hzG, r, s, hr, hs, _hcop, hrB, hsB, hgeom⟩ := mem_filter.mp hz
  refine mem_biUnion.mpr ⟨r, mem_Icc.mpr ⟨hr, hrB⟩,
    mem_biUnion.mpr ⟨s, mem_Icc.mpr ⟨hs, hsB⟩, mem_filter.mpr ⟨hzG, ?_⟩⟩⟩
  have hsum : r + s ≤ 2 * (L + 1) ^ 3 := by omega
  have hmul := Nat.mul_le_mul_right (D * (L + 1)) hsum
  have heq : 2 * (L + 1) ^ 3 * (D * (L + 1)) = radius D L := by unfold radius; ring
  have hnat : (r + s) * (D * (L + 1)) ≤ radius D L := hmul.trans_eq heq
  exact hgeom.trans (by exact_mod_cast hnat)

theorem card_bound (G : Finset ℕ) (D X L : ℕ) :
    (targets G D X L).card ≤ (L + 1) ^ 6 * (4 * D * (L + 1) ^ 4 + 1) := by
  have hinner (r : ℕ) (hr : r ∈ codes L) :
      ((codes L).biUnion fun s ↦ band G X r s (radius D L)).card ≤
        (codes L).card * (2 * radius D L + 1) :=
    card_biUnion_le_card_mul (codes L) _ _
      (fun s _ ↦ band_card G X r s _ (mem_Icc.mp hr).1)
  calc
    _ ≤ ((codes L).biUnion fun r ↦ (codes L).biUnion fun s ↦ band G X r s (radius D L)).card :=
      card_le_card (target_cover G D X L)
    _ ≤ (codes L).card * ((codes L).card * (2 * radius D L + 1)) :=
      card_biUnion_le_card_mul (codes L) _ _ hinner
    _ = _ := by rw [codes_card]; unfold radius; ring

theorem card_power_bound (G : Finset ℕ) (D X L : ℕ) :
    (targets G D X L).card ≤ (4 * D + 1) * (L + 1) ^ 10 := by
  have hp : (L + 1) ^ 6 ≤ (L + 1) ^ 10 :=
    Nat.pow_le_pow_right (by omega : 0 < L + 1) (by decide : 6 ≤ 10)
  calc
    _ ≤ (L + 1) ^ 6 * (4 * D * (L + 1) ^ 4 + 1) := card_bound G D X L
    _ = 4 * D * (L + 1) ^ 10 + (L + 1) ^ 6 := by ring
    _ ≤ 4 * D * (L + 1) ^ 10 + (L + 1) ^ 10 := Nat.add_le_add_left hp _
    _ = _ := by ring

end PaperP1.AlignedTargetCount
