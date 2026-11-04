module

public import PaperP1.Arithmetic.AsymmetricEvenLoss
public import PaperP1.Algebra.BinarySpanSelections

/-! # Positive asymmetric loss has an actual even new selection and a raw old selection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricLossSelections

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.AsymmetricEvenLoss

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem exists_selections {H z L : ℕ} {U : Finset ℕ} (hz : 0 < z)
    (hpos : 0 < loss H U z L) :
    ∃ A I : Finset ℕ, A ⊆ U ∧ I ⊆ NormalizedWindowSets.values z L ∧
      Even I.card ∧ 2 ≤ I.card ∧
      (∑ n ∈ I, largeParity H n) = ∑ n ∈ A, largeParity H n := by
  classical
  change 0 < Module.finrank F₂
    (Submodule.comap (EvenImage.evenMap (newData H z L)) (oldSpace H U)) at hpos
  obtain ⟨w, hw⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := F₂)
    (M := Submodule.comap (EvenImage.evenMap (newData H z L)) (oldSpace H U))).mp hpos
  have hwne : w.val ≠ 0 := fun he ↦ hw (Subtype.ext he)
  let J := BinaryEvenSelections.selected w.val.val
  have hJtwo : 2 ≤ J.card := BinaryEvenSelections.selected_card_two hwne
  have hJeven : Even J.card := (BinaryEvenSelections.even_selected_iff _).mpr w.val.property
  have hnew : (∑ i ∈ J, largeParity H (startCompleteVertexLabel z L i)) =
      EvenImage.evenMap (newData H z L) w.val := by
    change (∑ i ∈ J, newData H z L i) = EvenImage.combination (newData H z L) w.val.val
    rw [EvenImage.combination_apply]
    exact (BinarySpanSelections.weighted_selected_smul w.val.val (newData H z L)).symm
  obtain ⟨A, hA, hAeq⟩ := BinarySpanSelections.exists_subset_sum (largeParity H) U
    (EvenImage.evenMap (newData H z L) w.val) w.property
  let I := J.image (startCompleteVertexLabel z L)
  have hcard : I.card = J.card := card_image_of_injective J (startCompleteVertexLabel_injective hz)
  refine ⟨A, I, hA, ?_, by rwa [hcard], by omega, ?_⟩
  · intro n hn
    obtain ⟨i, _hi, rfl⟩ := mem_image.mp hn
    exact NormalizedWindowSets.mem_values.mpr ⟨i, rfl⟩
  · change (∑ n ∈ J.image (startCompleteVertexLabel z L), largeParity H n) = _
    rw [sum_image (startCompleteVertexLabel_injective hz).injOn]
    exact hnew.trans hAeq.symm

end PaperP1.AsymmetricLossSelections
