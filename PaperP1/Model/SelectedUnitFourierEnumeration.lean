module

public import PaperP1.Arithmetic.SelectedUnitWordBijection
public import PaperP1.Model.PrivateUnitCovariance

/-! # Literal enumeration of the actual signed unit Fourier sum by canonical words -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedUnitFourierEnumeration

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount
  PaperP1.ChannelPlacements PaperP1.ExactUnitProgression PaperP1.ChannelGapWords
  PaperP1.SelectedUnitWords PaperP1.SelectedUnitWordBijection PaperP1.UnitAffineSigns
  PaperP1.PrivateUnitCovariance

local instance selectedUnitFourierPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem weighted_selection_sum {a b x y L : ℕ} (ha : 0 < a) (hx : 0 < x) (hy : 0 < y)
    (s : Shapes a b x y L) (w : Words s.1.val) (f : ↥(units a b x y L) → F₂) :
    (∑ u, BinaryEvenSelections.coefficients (selection hx hy s w) u * f u) =
      ∑ k, w.val k * f (step hx hy s k) := by
  rw [BinaryEvenSelections.weighted_selected_sum, BinaryEvenSelections.selected_coefficients, selection,
    sum_image (fun k _ l _ h ↦ step_injective ha hx hy s h)]
  exact (BinaryEvenSelections.weighted_selected_sum w.val (fun k ↦ f (step hx hy s k))).symm

def kernelEquiv {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) :
    Encodings a b x y L ≃ {w : LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(units a b x y L)) // w ≠ 0} :=
  (canonicalEquiv ha hb hab hx hy).trans BinaryEvenSelections.nonemptyEvenEquiv.symm

theorem kernelEquiv_coefficients {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) (e : Encodings a b x y L) :
    (kernelEquiv ha hb hab hx hy e).val.val =
      BinaryEvenSelections.coefficients (selection (by omega) hy e.1 e.2) := rfl

theorem kernelEquiv_sign {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) (e : Encodings a b x y L) :
    binarySign (leftParity (kernelEquiv ha hb hab hx hy e).val +
      rightParity (kernelEquiv ha hb hab hx hy e).val) =
      placementSign e.1.2.val.val.1.val * placementSign e.1.2.val.val.2.val := by
  simp only [leftParity, rightParity, kernelEquiv_coefficients]
  rw [weighted_selection_sum ha (by omega) hy e.1 e.2,
    weighted_selection_sum ha (by omega) hy e.1 e.2]
  simp only [Fin.ext_iff, Fin.val_zero, step_left, step_right]
  exact word_sign ha hb _ _ e.2

theorem signed_unit_enumeration {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) :
    signedUnitSum a b x y L =
      ((∑ s : Shapes a b x y L, ChannelSumIdentity.weight s.1.val *
        placementSign s.2.val.val.1.val * placementSign s.2.val.val.2.val : ℤ) : ℝ) := by
  let f : LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(units a b x y L)) → ℝ :=
    fun w ↦ (binarySign (leftParity w + rightParity w) : ℝ)
  have hnonzero : signedUnitSum a b x y L = ∑ w : {w : LinearMap.ker
      (EvenSupportRank.sumMap F₂ ↥(units a b x y L)) // w ≠ 0}, f w.val := by
    unfold signedUnitSum
    change (∑ w, if w ≠ 0 then f w else 0) = _
    rw [← sum_filter]
    exact sum_subtype _ (by intro w; simp only [mem_filter, mem_univ, true_and]) f
  rw [hnonzero]
  calc
    _ = ∑ e : Encodings a b x y L, f (kernelEquiv ha hb hab hx hy e).val := by
      symm
      apply Fintype.sum_equiv (kernelEquiv ha hb hab hx hy)
      intro e
      rfl
    _ = ∑ e : Encodings a b x y L,
        ((placementSign e.1.2.val.val.1.val * placementSign e.1.2.val.val.2.val : ℤ) : ℝ) := by
      apply sum_congr rfl
      intro e _
      exact congrArg (fun z : ℤ ↦ (z : ℝ)) (kernelEquiv_sign ha hb hab hx hy e)
    _ = _ := by
      change (∑ e : (Σ s : Shapes a b x y L, Words s.1.val),
        ((placementSign e.1.2.val.val.1.val * placementSign e.1.2.val.val.2.val : ℤ) : ℝ)) = _
      rw [Fintype.sum_sigma, Int.cast_sum]
      apply sum_congr rfl
      intro s _
      dsimp only
      rw [sum_const, nsmul_eq_mul, card_univ,
        weight_eq_word_card (by have hd := (mem_Icc.mp s.1.property).1; omega)]
      push_cast
      ring

end PaperP1.SelectedUnitFourierEnumeration
