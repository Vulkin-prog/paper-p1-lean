module

public import PaperP1.Arithmetic.SmallChannelUniqueness
public import PaperP1.Arithmetic.UnitIntersectionRankLower
public import PaperP1.Arithmetic.ActualOffsetNonalignment

/-! # Deleting all double exact units costs only the actual proper intersection rank

At a distant scale all double-unit channels have the same small rational slope.
One literal unit set therefore covers all their physical positions.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExactUnitDeletion

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount

def NoExactAway (x y L : ℕ) (A B : Finset (Fin (L + 1))) : Prop :=
  ∀ u₁ u₂ v₁ v₂ : Fin (L + 1), u₁ ∉ A → u₂ ∉ A → v₁ ∉ B → v₂ ∉ B →
    (offset u₁, offset v₁) ≠ (offset u₂, offset v₂) →
    ((x : ℤ) + offset u₁) * ((y : ℤ) + offset v₂) ≠
      ((x : ℤ) + offset u₂) * ((y : ℤ) + offset v₁)

theorem cover_double_units (N x y L a b : ℕ) (hN : 0 < N)
    (hx : x ∈ Model.dyadicBlock N) (hy : y ∈ Model.dyadicBlock N)
    (hxB : L + 1 < x) (hyB : L + 1 < y) (hlarge : 16 * (L + 1) ^ 3 < N)
    (ha : 0 < a) (_hb : 0 < b) (haB : a ≤ 2 * (L + 1)) (hbB : b ≤ 2 * (L + 1))
    (hu : (units a b x y L).Nonempty)
    (u₁ u₂ v₁ v₂ : Fin (L + 1)) (hne : (u₁, v₁) ≠ (u₂, v₂))
    (he : startCompleteVertexLabel x L u₁ * startCompleteVertexLabel y L v₂ =
      startCompleteVertexLabel x L u₂ * startCompleteVertexLabel y L v₁) :
    (u₁, v₁) ∈ units a b x y L ∧ (u₂, v₂) ∈ units a b x y L := by
  obtain ⟨c, d, hc, hd, _hcop, hcB, hdB, h₁, h₂⟩ :=
    SmallExactUnitAlignment.two_units x y L hxB hyB u₁ u₂ v₁ v₂ hne he
  have hgeom₁ := SmallChannelUniqueness.unit_geometric hN hx hy hu
  have hgeom₂ := SmallChannelUniqueness.unit_geometric hN hx hy ⟨(u₁, v₁), h₁⟩
  have hslope := SmallChannelUniqueness.same_slope a b c d x y L haB hbB hcB hdB
    (hlarge.trans_le (mem_Ico.mp hy).1) hgeom₁ hgeom₂
  have hsets := SmallChannelUniqueness.units_eq_of_slope (x := x) (y := y) (L := L) ha hd hslope
  rw [hsets]
  exact ⟨h₁, h₂⟩

theorem pair_deletion (N x y L : ℕ) (hN : 0 < N)
    (hx : x ∈ Model.dyadicBlock N) (hy : y ∈ Model.dyadicBlock N)
    (hxB : L + 1 < x) (hyB : L + 1 < y) (hlarge : 16 * (L + 1) ^ 3 < N)
    (hdefect : Module.finrank F₂ (WindowRelationCode.windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    ∃ A B : Finset (Fin (L + 1)),
      A.card + B.card ≤ 2 * (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) + 2) ∧
      NoExactAway x y L A B := by
  classical
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hcast (u₁ u₂ v₁ v₂ : Fin (L + 1))
      (he : ((x : ℤ) + offset u₁) * ((y : ℤ) + offset v₂) =
        ((x : ℤ) + offset u₂) * ((y : ℤ) + offset v₁)) :
      startCompleteVertexLabel x L u₁ * startCompleteVertexLabel y L v₂ =
        startCompleteVertexLabel x L u₂ * startCompleteVertexLabel y L v₁ := by
    have hz : (startCompleteVertexLabel x L u₁ : ℤ) * (startCompleteVertexLabel y L v₂ : ℤ) =
        (startCompleteVertexLabel x L u₂ : ℤ) * (startCompleteVertexLabel y L v₁ : ℤ) := by
      simpa only [label_cast hxpos, label_cast hypos] using he
    exact_mod_cast hz
  by_cases hdouble : ∃ u₁ u₂ v₁ v₂ : Fin (L + 1), (u₁, v₁) ≠ (u₂, v₂) ∧
      startCompleteVertexLabel x L u₁ * startCompleteVertexLabel y L v₂ =
        startCompleteVertexLabel x L u₂ * startCompleteVertexLabel y L v₁
  · obtain ⟨u₁, u₂, v₁, v₂, hne, he⟩ := hdouble
    obtain ⟨a, b, ha, hb, _hcop, haB, hbB, hu, _hv⟩ :=
      SmallExactUnitAlignment.two_units x y L hxB hyB u₁ u₂ v₁ v₂ hne he
    let D := units a b x y L
    let A := D.image Prod.fst
    let B := D.image Prod.snd
    have hD := UnitIntersectionRankLower.unit_count_le_intersection_add_two ha hb
      (by omega : 2 ≤ x) (by omega : 2 ≤ y) hdefect
    refine ⟨A, B, ?_, ?_⟩
    · have hA : A.card ≤ D.card := card_image_le
      have hB : B.card ≤ D.card := card_image_le
      change D.card ≤ _ at hD
      omega
    · intro r₁ r₂ s₁ s₂ hr₁ _hr₂ _hs₁ _hs₂ hrs heq
      have hne' : (r₁, s₁) ≠ (r₂, s₂) := by
        intro hh
        exact hrs (congrArg (fun p : Fin (L + 1) × Fin (L + 1) ↦ (offset p.1, offset p.2)) hh)
      have hcovered := cover_double_units N x y L a b hN hx hy hxB hyB hlarge ha hb haB hbB
        ⟨(u₁, v₁), hu⟩ r₁ r₂ s₁ s₂ hne' (hcast r₁ r₂ s₁ s₂ heq)
      exact hr₁ (mem_image.mpr ⟨(r₁, s₁), hcovered.1, rfl⟩)
  · refine ⟨∅, ∅, by simp, ?_⟩
    intro r₁ r₂ s₁ s₂ _hr₁ _hr₂ _hs₁ _hs₂ hrs heq
    apply hdouble
    refine ⟨r₁, r₂, s₁, s₂, ?_, hcast r₁ r₂ s₁ s₂ heq⟩
    intro hh
    exact hrs (congrArg (fun p : Fin (L + 1) × Fin (L + 1) ↦ (offset p.1, offset p.2)) hh)

end PaperP1.ExactUnitDeletion
