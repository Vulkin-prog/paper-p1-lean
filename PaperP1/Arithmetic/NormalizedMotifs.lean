module

public import PaperP1.Arithmetic.NormalizedUnitCount

/-! # Fixed finite offset motifs for every normalized two-window union -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedMotifs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount

def motif (a b L : ℕ) (i j : Fin (L + 1)) : Finset ℤ :=
  (univ.image fun v : Fin (L + 1) ↦ (b : ℤ) * ((v.val : ℤ) - i.val)) ∪
    (univ.image fun v : Fin (L + 1) ↦ (a : ℤ) * ((v.val : ℤ) - j.val))

def family (a b L : ℕ) : Finset (Finset ℤ) :=
  univ.image fun ij : Fin (L + 1) × Fin (L + 1) ↦ motif a b L ij.1 ij.2

theorem motif_mem_family (a b L : ℕ) (i j : Fin (L + 1)) : motif a b L i j ∈ family a b L :=
  mem_image.mpr ⟨(i, j), mem_univ _, rfl⟩

theorem family_card (a b L : ℕ) : (family a b L).card ≤ (L + 1) ^ 2 := by
  exact card_image_le.trans (by simp only [card_univ, Fintype.card_prod, Fintype.card_fin, pow_two, le_refl])

theorem offset_difference_bound {L : ℕ} (u v : Fin (L + 1)) : |(u.val : ℤ) - v.val| ≤ L := by
  apply abs_le.mpr
  have hu := u.isLt
  have hv := v.isLt
  omega

theorem motif_bound {a b L : ℕ} (hab : a ≤ b) (i j : Fin (L + 1)) (z : ℤ) (hz : z ∈ motif a b L i j) :
    |z| ≤ (b : ℤ) * L := by
  rcases mem_union.mp hz with hz | hz
  · obtain ⟨v, _, rfl⟩ := mem_image.mp hz
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ b)]
    exact mul_le_mul_of_nonneg_left (offset_difference_bound v i) (by positivity)
  · obtain ⟨v, _, rfl⟩ := mem_image.mp hz
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ a)]
    exact (mul_le_mul_of_nonneg_left (offset_difference_bound v j) (by positivity)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (by positivity))

theorem normalized_integer_image (c x L : ℕ) :
    (normalized c x L).image (fun n : ℕ ↦ (n : ℤ)) =
      univ.image (fun v : Fin (L + 1) ↦ ((c * startCompleteVertexLabel x L v : ℕ) : ℤ)) := by
  simp only [normalized, FiniteEvenSquareClasses.dilate, values, image_image, Function.comp_def]

theorem translated_motif {a b x y L : ℕ} (hx : 0 < x) (hy : 0 < y)
    (i j : Fin (L + 1)) (hunit : b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j) :
    (union a b x y L).image (fun n : ℕ ↦ (n : ℤ)) =
      (motif a b L i j).image (fun z ↦ ((b * startCompleteVertexLabel x L i : ℕ) : ℤ) + z) := by
  have hleft : (fun v : Fin (L + 1) ↦ ((b * startCompleteVertexLabel x L v : ℕ) : ℤ)) =
      (fun v ↦ ((b * startCompleteVertexLabel x L i : ℕ) : ℤ) + (b : ℤ) * ((v.val : ℤ) - i.val)) := by
    funext v
    push_cast
    rw [label_cast hx, label_cast hx]
    unfold offset
    ring
  have hright : (fun v : Fin (L + 1) ↦ ((a * startCompleteVertexLabel y L v : ℕ) : ℤ)) =
      (fun v ↦ ((b * startCompleteVertexLabel x L i : ℕ) : ℤ) + (a : ℤ) * ((v.val : ℤ) - j.val)) := by
    funext v
    rw [hunit]
    push_cast
    rw [label_cast hy, label_cast hy]
    unfold offset
    ring
  rw [NormalizedWindowSets.union, image_union, normalized_integer_image, normalized_integer_image, motif, image_union, image_image, image_image]
  exact congrArg₂ (fun S T : Finset ℤ ↦ S ∪ T) (congrArg (fun f : Fin (L + 1) → ℤ ↦ univ.image f) hleft)
    (congrArg (fun f : Fin (L + 1) → ℤ ↦ univ.image f) hright)

theorem finite_translation_pattern {a b x y L : ℕ} (hab : a ≤ b) (hx : 0 < x) (hy : 0 < y)
    (hunits : (units a b x y L).Nonempty) :
    ∃ M ∈ family a b L, ∃ t : ℤ,
      (union a b x y L).image (fun n : ℕ ↦ (n : ℤ)) = M.image (fun z ↦ t + z) ∧
        ∀ z ∈ M, |z| ≤ (b : ℤ) * L := by
  obtain ⟨u, hu⟩ := hunits
  refine ⟨motif a b L u.1 u.2, motif_mem_family _ _ _ _ _,
    ((b * startCompleteVertexLabel x L u.1 : ℕ) : ℤ), translated_motif hx hy u.1 u.2 (mem_units.mp hu), ?_⟩
  exact motif_bound hab u.1 u.2

theorem centres_determined_by_anchor {a b x y x' y' L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) (hx' : 0 < x') (hy' : 0 < y') (i j : Fin (L + 1))
    (hu : b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j)
    (hu' : b * startCompleteVertexLabel x' L i = a * startCompleteVertexLabel y' L j)
    (hanchor : b * startCompleteVertexLabel x L i = b * startCompleteVertexLabel x' L i) :
    x = x' ∧ y = y' := by
  have hleft := mul_left_cancel₀ hb.ne' hanchor
  have hright := mul_left_cancel₀ ha.ne' (hu.symm.trans (hanchor.trans hu'))
  rw [startCompleteVertexLabel_eq_offset hx, startCompleteVertexLabel_eq_offset hx'] at hleft
  rw [startCompleteVertexLabel_eq_offset hy, startCompleteVertexLabel_eq_offset hy'] at hright
  omega

theorem anchor_injective {a b L : ℕ} (ha : 0 < a) (hb : 0 < b) (i j : Fin (L + 1)) :
    Set.InjOn (fun xy : ℕ × ℕ ↦ b * startCompleteVertexLabel xy.1 L i)
      {xy | 0 < xy.1 ∧ 0 < xy.2 ∧
        b * startCompleteVertexLabel xy.1 L i = a * startCompleteVertexLabel xy.2 L j} := by
  intro xy hxy xy' hxy' heq
  obtain ⟨hx, hy⟩ := centres_determined_by_anchor ha hb hxy.1 hxy.2.1 hxy'.1 hxy'.2.1 i j hxy.2.2 hxy'.2.2 heq
  exact Prod.ext hx hy

end PaperP1.NormalizedMotifs
