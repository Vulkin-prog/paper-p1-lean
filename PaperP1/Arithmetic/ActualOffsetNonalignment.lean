module

public import PaperP1.Arithmetic.BoundedPointAlignment
public import PaperP1.Arithmetic.TwoPointSquareClasses

/-! # Exact offset lines in actual windows

The nonalignment statement concerns actual positions, with their integer offsets.
The disjoint-space variant needs only two-point independence, not full window rank.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualOffsetNonalignment

open PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount

def NoExact (x y L : ℕ) : Prop :=
  ∀ u₁ u₂ v₁ v₂ : Fin (L + 1), (offset u₁, offset v₁) ≠ (offset u₂, offset v₂) →
    ((x : ℤ) + offset u₁) * ((y : ℤ) + offset v₂) ≠
      ((x : ℤ) + offset u₂) * ((y : ℤ) + offset v₁)

theorem NoExact.symm {x y L : ℕ} (h : NoExact x y L) : NoExact y x L := by
  intro u₁ u₂ v₁ v₂ hne he
  apply h v₁ v₂ u₁ u₂
  · intro hh
    exact hne (Prod.ext (congrArg Prod.snd hh) (congrArg Prod.fst hh))
  · simpa only [mul_comm] using he.symm

theorem of_nonaligned {x y L : ℕ} (hL : 1 ≤ L)
    (hx : L + 1 < x) (hy : L + 1 < y)
    (hno : ¬CompressedTargetAlignment.Aligned 1 x y L) : NoExact x y L := by
  intro u₁ u₂ v₁ v₂ hne he
  apply hno
  apply BoundedPointAlignment.source_alignment hL
  apply BoundedPointAlignment.alignment_of_cross (L + 1) (x : ℤ) (y : ℤ)
    (-offset u₁, -offset v₁) (-offset u₂, -offset v₂)
    (by exact_mod_cast hx) (by exact_mod_cast hy)
    ⟨by simpa only [abs_neg] using EnlargedPairGeometry.offset_abs u₁,
      by simpa only [abs_neg] using EnlargedPairGeometry.offset_abs v₁⟩
    ⟨by simpa only [abs_neg] using EnlargedPairGeometry.offset_abs u₂,
      by simpa only [abs_neg] using EnlargedPairGeometry.offset_abs v₂⟩
  · intro h
    apply hne
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    exact Prod.ext (neg_injective h₁) (neg_injective h₂)
  · dsimp only
    nlinarith only [he]

theorem of_disjoint {x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (htwo : ∀ u v : Fin (L + 1), u ≠ v →
      parityVec (startCompleteVertexLabel x L u) + parityVec (startCompleteVertexLabel x L v) ≠ 0)
    (hdis : Disjoint (squareClassSpace x L) (squareClassSpace y L)) : NoExact x y L := by
  intro u₁ u₂ v₁ v₂ hne he
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hnx (u : Fin (L + 1)) : startCompleteVertexLabel x L u ≠ 0 := by
    rw [startCompleteVertexLabel_eq_offset hxpos]
    omega
  have hny (v : Fin (L + 1)) : startCompleteVertexLabel y L v ≠ 0 := by
    rw [startCompleteVertexLabel_eq_offset hypos]
    omega
  have hcross : startCompleteVertexLabel x L u₁ * startCompleteVertexLabel y L v₂ =
      startCompleteVertexLabel x L u₂ * startCompleteVertexLabel y L v₁ := by
    have hz : ((startCompleteVertexLabel x L u₁ : ℕ) : ℤ) *
        ((startCompleteVertexLabel y L v₂ : ℕ) : ℤ) =
        ((startCompleteVertexLabel x L u₂ : ℕ) : ℤ) *
          ((startCompleteVertexLabel y L v₁ : ℕ) : ℤ) := by
      simpa only [label_cast hxpos, label_cast hypos] using he
    exact_mod_cast hz
  have hu : u₁ ≠ u₂ := by
    intro hh
    subst u₂
    have hv : v₂ = v₁ := startCompleteVertexLabel_injective hypos
      (mul_left_cancel₀ (hnx u₁) hcross)
    exact hne (Prod.ext rfl (congrArg offset hv.symm))
  have hclass := TwoPointSquareClasses.parity_pair_eq_of_cross_product
    (hnx u₁) (hnx u₂) (hny v₁) (hny v₂) hcross
  have hmemx := TwoPointSquareClasses.pair_class_mem x L u₁ u₂
  have hmemy := TwoPointSquareClasses.pair_class_mem y L v₁ v₂
  rw [← hclass] at hmemy
  exact htwo u₁ u₂ hu ((Submodule.disjoint_def.mp hdis) _ hmemx hmemy)

end PaperP1.ActualOffsetNonalignment
