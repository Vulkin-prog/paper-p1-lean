module

public import PaperP1.Affine.RetainedNullity

/-! # Effective nullity is preserved by an injective finite relabelling -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InjectiveNullityTransport

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank

variable {U ι κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]

theorem nullity_image (S : κ → Submodule 𝔽₂ U) [∀ k, Fintype (S k)]
    (f : ι → κ) (hf : Function.Injective f) (A : Finset ι) :
    relativeNullityOn (fun i ↦ S (f i)) A = relativeNullityOn S (A.image f) := by
  have hleft := rank_add_nullity_on (fun i ↦ S (f i)) A
  have hright := rank_add_nullity_on S (A.image f)
  rw [rank_image, sum_image hf.injOn] at hright
  omega

theorem image_ssubset (f : ι → κ) (hf : Function.Injective f) {A B : Finset ι}
    (hAB : A ⊂ B) : A.image f ⊂ B.image f := by
  apply ssubset_iff_subset_ne.mpr
  refine ⟨image_subset_image hAB.subset, ?_⟩
  intro heq
  have hc := congrArg Finset.card heq
  rw [card_image_of_injective A hf, card_image_of_injective B hf] at hc
  have hlt := card_lt_card hAB
  omega

end PaperP1.InjectiveNullityTransport
