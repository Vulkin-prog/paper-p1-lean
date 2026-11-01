module

public import PaperP1.Arithmetic.SelectedUnitExtrema
public import PaperP1.Arithmetic.ChannelGapWords

/-! # Endpoint-selected words on actual exact-unit segments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedUnitWords

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount
  PaperP1.ChannelPlacements PaperP1.ExactUnitProgression PaperP1.ChannelGapWords
  PaperP1.SelectedUnitExtrema

local instance selectedUnitWordsPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Shapes (a b x y L : ℕ) :=
  Σ d : ↥(Icc 1 (L / b)),
    {u : ↥(units a b x y L) // u.val.1.val ∈ placements L (a * d.val) ∧
      u.val.2.val ∈ placements L (b * d.val)}

instance shapesFintype (a b x y L : ℕ) : Fintype (Shapes a b x y L) := by
  unfold Shapes
  infer_instance

theorem fits_of_placement {L D i : ℕ} (hi : i ∈ placements L D) : i + D ≤ L := by
  unfold placements at hi
  split at hi
  · have h := mem_range.mp hi
    omega
  · simp at hi

def step {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (s : Shapes a b x y L)
    (k : Fin (s.1.val + 1)) : ↥(units a b x y L) :=
  stepUnit hx hy s.2.val k.val
    (by have h := fits_of_placement s.2.property.1; have hk := k.isLt; nlinarith)
    (by have h := fits_of_placement s.2.property.2; have hk := k.isLt; nlinarith)

theorem step_left {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (s : Shapes a b x y L)
    (k : Fin (s.1.val + 1)) : (step hx hy s k).val.1.val = s.2.val.val.1.val + a * k.val := rfl

theorem step_right {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (s : Shapes a b x y L)
    (k : Fin (s.1.val + 1)) : (step hx hy s k).val.2.val = s.2.val.val.2.val + b * k.val := rfl

theorem step_zero {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (s : Shapes a b x y L) :
    step hx hy s 0 = s.2.val := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> simp only [step_left, step_right, Fin.val_zero, mul_zero, add_zero]

theorem step_injective {a b x y L : ℕ} (ha : 0 < a) (hx : 0 < x) (hy : 0 < y)
    (s : Shapes a b x y L) : Function.Injective (step hx hy s) := by
  intro k l h
  have hv := congrArg (fun u : ↥(units a b x y L) ↦ u.val.1.val) h
  rw [step_left, step_left] at hv
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left ha (Nat.add_left_cancel hv))

def selection {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (s : Shapes a b x y L)
    (w : Words s.1.val) : Finset ↥(units a b x y L) :=
  (BinaryEvenSelections.selected w.val).image (step hx hy s)

theorem mem_selection {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (s : Shapes a b x y L)
    (w : Words s.1.val) (u : ↥(units a b x y L)) :
    u ∈ selection hx hy s w ↔ ∃ k, w.val k ≠ 0 ∧ step hx hy s k = u := by
  simp only [selection, mem_image, BinaryEvenSelections.selected, mem_filter, mem_univ, true_and]

theorem first_mem_selection {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (s : Shapes a b x y L)
    (w : Words s.1.val) : s.2.val ∈ selection hx hy s w := by
  apply (mem_selection hx hy s w _).mpr
  exact ⟨0, by rw [w.property.1]; exact one_ne_zero, step_zero hx hy s⟩

theorem last_mem_selection {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (s : Shapes a b x y L)
    (w : Words s.1.val) : step hx hy s (Fin.last s.1.val) ∈ selection hx hy s w := by
  apply (mem_selection hx hy s w _).mpr
  exact ⟨Fin.last s.1.val, by rw [w.property.2.1]; exact one_ne_zero, rfl⟩

theorem selection_even {a b x y L : ℕ} (ha : 0 < a) (hx : 0 < x) (hy : 0 < y)
    (s : Shapes a b x y L) (w : Words s.1.val) : Even (selection hx hy s w).card := by
  rw [selection, card_image_of_injective _ (step_injective ha hx hy s),
    BinaryEvenSelections.even_selected_iff, LinearMap.mem_ker, EvenSupportRank.sumMap_apply]
  exact w.property.2.2

def selectionBounds {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (s : Shapes a b x y L)
    (w : Words s.1.val) : Bounds (selection hx hy s w) where
  first := s.2.val
  last := step hx hy s (Fin.last s.1.val)
  first_mem := first_mem_selection hx hy s w
  last_mem := last_mem_selection hx hy s w
  first_le := by
    intro u hu
    obtain ⟨k, _, rfl⟩ := (mem_selection hx hy s w u).mp hu
    change s.2.val.val.1.val ≤ (step hx hy s k).val.1.val
    rw [step_left]
    omega
  le_last := by
    intro u hu
    obtain ⟨k, _, rfl⟩ := (mem_selection hx hy s w u).mp hu
    change (step hx hy s k).val.1.val ≤ (step hx hy s (Fin.last s.1.val)).val.1.val
    rw [step_left, step_left]
    have hk := k.isLt
    simp only [Fin.val_last]
    nlinarith

theorem coefficient_at_step {a b x y L : ℕ} (ha : 0 < a) (hx : 0 < x) (hy : 0 < y)
    (s : Shapes a b x y L) (w : Words s.1.val) (k : Fin (s.1.val + 1)) :
    BinaryEvenSelections.coefficients (selection hx hy s w) (step hx hy s k) = w.val k := by
  have hmem : step hx hy s k ∈ selection hx hy s w ↔ w.val k ≠ 0 := by
    rw [mem_selection]
    constructor
    · rintro ⟨l, hl, heq⟩
      exact (step_injective ha hx hy s heq) ▸ hl
    · intro hk
      exact ⟨k, hk, rfl⟩
  rcases BinaryEvenSelections.binary_bit (w.val k) with h | h <;>
    simp [BinaryEvenSelections.coefficients, hmem, h]

end PaperP1.SelectedUnitWords
