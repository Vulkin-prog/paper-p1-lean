module

public import PaperP1.Algebra.FinitePiExtension

/-! # Matched coordinates give an exact lower bound for an even-selection preimage

Every selected coordinate already lying in the old space contributes its
zero-sum selections to the preimage. No independence of the selected values
or injectivity of their square-class map is needed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenPreimageRank

open Finset

variable {K ι E : Type*} [DivisionRing K] [Fintype ι] [AddCommGroup E] [Module K E]

theorem selected_lower (data : ι → E) (S : Submodule K E) (I : Finset ι)
    (hI : ∀ i ∈ I, data i ∈ S) :
    I.card - 1 ≤ Module.finrank K (Submodule.comap (EvenImage.evenMap data) S) := by
  classical
  let e : I ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  let f := FinitePiExtension.extendEven (K := K) e
  have hsub : LinearMap.range f ≤ Submodule.comap (EvenImage.evenMap data) S := by
    rintro _ ⟨w, rfl⟩
    change EvenImage.evenMap data (FinitePiExtension.extendEven e w) ∈ S
    rw [FinitePiExtension.evenMap_extend e (fun i : I ↦ data i.val) data (fun _ ↦ rfl)]
    change EvenImage.combination (fun i : I ↦ data i.val) w.val ∈ S
    rw [EvenImage.combination_apply]
    exact Submodule.sum_mem S (fun i _ ↦ Submodule.smul_mem S _ (hI i.val i.property))
  have hd := Submodule.finrank_mono hsub
  rw [LinearMap.finrank_range_of_inj (FinitePiExtension.extendEven_injective e),
    EvenSupportRank.kernel_sum_finrank, Fintype.card_coe] at hd
  exact hd

end PaperP1.EvenPreimageRank
