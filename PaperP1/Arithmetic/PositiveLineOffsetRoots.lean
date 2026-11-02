module

public import PaperP1.Arithmetic.PositiveLineSplitProducts
public import PaperP1.Arithmetic.OffsetRootExceptionalSet
public import PaperP1.Combinatorics.DiscardTouchedSupports

/-! # Three disjoint offset equations leave one nondegenerate integer split product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveLineOffsetRoots

open Finset PaperP1.Arithmetic PaperP1.OffsetRootExceptionalSet PaperP1.OffsetRootSeparation

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def integerOffset {L : ℕ} (u : Fin (L + 1)) : ℤ := u.val - 1

def integerOffsets {L : ℕ} (P : Finset (Fin (L + 1))) : Finset ℤ := P.image integerOffset

def coordinates {L : ℕ} (P Q : Finset (Fin (L + 1))) : Finset (Coordinate L) :=
  P.image Sum.inl ∪ Q.image Sum.inr

def shift {L : ℕ} (a b : ℕ) (c : ℤ) : Coordinate L → ℤ :=
  Sum.elim (fun u ↦ (a : ℤ) * integerOffset u) (fun v ↦ c + (b : ℤ) * integerOffset v)

theorem integerOffset_injective (L : ℕ) : Function.Injective (integerOffset (L := L)) := by
  intro u v hh
  apply Fin.ext
  dsimp [integerOffset] at hh
  omega

theorem cast_integerOffset {L : ℕ} (u : Fin (L + 1)) : (integerOffset u : ℚ) = offset u := by
  simp only [integerOffset, offset, Int.cast_sub, Int.cast_natCast, Int.cast_one]

theorem mem_coordinates_left {L : ℕ} (P Q : Finset (Fin (L + 1))) (u : Fin (L + 1)) :
    Sum.inl u ∈ coordinates P Q ↔ u ∈ P := by simp [coordinates]

theorem mem_coordinates_right {L : ℕ} (P Q : Finset (Fin (L + 1))) (u : Fin (L + 1)) :
    Sum.inr u ∈ coordinates P Q ↔ u ∈ Q := by simp [coordinates]

theorem coordinates_pairwise_disjoint {ι : Type*} [DecidableEq ι] {L : ℕ} (I : Finset ι)
    (P Q : ι → Finset (Fin (L + 1)))
    (hP : (↑I : Set ι).PairwiseDisjoint P) (hQ : (↑I : Set ι).PairwiseDisjoint Q) :
    (↑I : Set ι).PairwiseDisjoint (fun i ↦ coordinates (P i) (Q i)) := by
  intro i hi j hj hij
  apply disjoint_left.mpr
  intro v hv hvj
  cases v with
  | inl u =>
    exact disjoint_left.mp (hP hi hj hij) ((mem_coordinates_left _ _ _).mp hv) ((mem_coordinates_left _ _ _).mp hvj)
  | inr u =>
    exact disjoint_left.mp (hQ hi hj hij) ((mem_coordinates_right _ _ _).mp hv) ((mem_coordinates_right _ _ _).mp hvj)

theorem shift_root {L a b : ℕ} (ha : 0 < a) (hb : 0 < b) (c : ℤ) (u : Coordinate L) :
    (shift a b c u : ℚ) = -(a : ℚ) * root ((a : ℚ) / b) ((c : ℚ) / b) u := by
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  cases u with
  | inl v =>
    simp only [shift, root, Sum.elim_inl, Int.cast_mul, Int.cast_natCast, cast_integerOffset, leftRoot]
    ring
  | inr v =>
    simp only [shift, root, Sum.elim_inr, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      cast_integerOffset, rightRoot]
    field_simp

theorem shift_injective_of_root {L a b : ℕ} (ha : 0 < a) (hb : 0 < b) (c : ℤ)
    (S : Finset (Coordinate L))
    (hinj : Set.InjOn (root ((a : ℚ) / b) ((c : ℚ) / b)) (↑S : Set (Coordinate L))) :
    Set.InjOn (shift (L := L) a b c) (↑S : Set (Coordinate L)) := by
  intro u hu v hv heq
  have hcast : (shift a b c u : ℚ) = shift a b c v := by exact_mod_cast heq
  rw [shift_root ha hb c u, shift_root ha hb c v] at hcast
  exact hinj hu hv (mul_left_cancel₀ (neg_ne_zero.mpr (by exact_mod_cast ha.ne')) hcast)

theorem exists_surviving {ι : Type*} [DecidableEq ι] {L a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (c : ℤ) (x y : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hinj : Function.Injective (evenSquareClassMap x L))
    (hdirect : Disjoint (squareClassSpace x L) (squareClassSpace y L))
    (hline : (b : ℤ) * y = (a : ℤ) * x + c) (I : Finset ι) (hI : 3 ≤ I.card)
    (S : ι → Finset (Coordinate L)) (hdisj : (↑I : Set ι).PairwiseDisjoint S) :
    ∃ i ∈ I, Set.InjOn (shift (L := L) a b c) (↑(S i) : Set (Coordinate L)) := by
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hlineQ : (y : ℚ) = (a : ℚ) / b * x + (c : ℚ) / b := by
    have hc : (b : ℚ) * y = (a : ℚ) * x + c := by exact_mod_cast hline
    field_simp
    nlinarith only [hc]
  obtain ⟨H, hHcard, hroot⟩ := exists_exceptional_coordinates x y L hx hy hinj hdirect
    ((a : ℚ) / b) ((c : ℚ) / b) (div_ne_zero haq hbq) hlineQ
  obtain ⟨D, _hDI, hDcard, havoid⟩ := DiscardTouchedSupports.exists_discard I S H hdisj
  obtain ⟨i, hi⟩ := sdiff_nonempty_of_card_lt_card (show D.card < I.card by omega)
  refine ⟨i, (mem_sdiff.mp hi).1, shift_injective_of_root ha hb c (S i) ?_⟩
  intro u hu v hv heq
  exact hroot (havoid i hi u hu) (havoid i hi v hv) heq

theorem disjoint_scaled_images {L a b : ℕ} (c : ℤ) (P Q : Finset (Fin (L + 1)))
    (hinj : Set.InjOn (shift (L := L) a b c) (↑(coordinates P Q) : Set (Coordinate L))) :
    Disjoint ((integerOffsets P).image fun u ↦ (a : ℤ) * u)
      ((integerOffsets Q).image fun v ↦ c + (b : ℤ) * v) := by
  rw [integerOffsets, integerOffsets, image_image, image_image]
  apply disjoint_left.mpr
  intro z hzP hzQ
  obtain ⟨u, hu, huZ⟩ := mem_image.mp hzP
  obtain ⟨v, hv, hvZ⟩ := mem_image.mp hzQ
  have hh : Sum.inl u = Sum.inr v := hinj
    ((mem_coordinates_left P Q u).mpr hu) ((mem_coordinates_right P Q v).mpr hv) (huZ.trans hvZ.symm)
  cases hh

end PaperP1.PositiveLineOffsetRoots
