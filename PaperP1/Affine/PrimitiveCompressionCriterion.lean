module

public import PaperP1.Affine.MinimalRelativeRelations
public import PaperP1.Affine.RetainedNullity

/-! # The exact proper-subfamily criterion for a primitive family with one compressed source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveCompressionCriterion

open Finset PaperP1.Affine PaperP1.MinimalRelativeRelations

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]
variable (W : Submodule 𝔽₂ U) [Fintype W] (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

local instance augmentedFintype (i : Option κ) : Fintype (augmented W S i) := by
  cases i with
  | none => exact inferInstanceAs (Fintype W)
  | some i => exact inferInstanceAs (Fintype (S i))

theorem nullity_some_image (A : Finset κ) :
    relativeNullityOn (augmented W S) (A.image some) = relativeNullityOn S A := by
  classical
  have h := rank_add_nullity_on (augmented W S) (A.image some)
  rw [sum_image (fun _ _ _ _ h ↦ Option.some.inj h), SubspaceFamilyRank.rank, SubspaceFamilyRank.span_image] at h
  have hbase := rank_add_nullity_on S A
  change SubspaceFamilyRank.rank S A + relativeNullityOn (augmented W S) (A.image some) =
    ∑ i ∈ A, Module.finrank 𝔽₂ (S i) at h
  omega

omit [Fintype W] [∀ i, Fintype (S i)] in
theorem indices_ssubset (B A : Finset κ) (hBA : B ⊂ A) : indices B ⊂ indices A := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro i hi
    cases i with
    | none => simp [indices]
    | some x =>
      have hx : x ∈ B := by simpa [indices] using hi
      simp [indices, hBA.subset hx]
  · intro heq
    apply hBA.ne
    apply Subset.antisymm hBA.subset
    intro x hx
    have hi : some x ∈ indices A := by simp [indices, hx]
    rw [← heq] at hi
    simpa [indices] using hi

theorem primitive_iff (A : Finset κ) :
    (0 < relativeNullityOn (augmented W S) (indices A) ∧
      ∀ J : Finset (Option κ), J ⊂ indices A → relativeNullityOn (augmented W S) J = 0) ↔
    relativeNullityOn S A = 0 ∧ 0 < nullity W S A ∧
      ∀ B : Finset κ, B ⊂ A → nullity W S B = 0 := by
  classical
  constructor
  · rintro ⟨hpos, hproper⟩
    have hsome : A.image some ⊂ indices A := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨subset_insert _ _, ?_⟩
      intro heq
      have hi : none ∈ indices A := mem_insert_self _ _
      rw [← heq] at hi
      simp at hi
    have hz := hproper (A.image some) hsome
    rw [nullity_some_image W S A] at hz
    exact ⟨hz, hpos, fun B hB ↦ hproper (indices B) (indices_ssubset B A hB)⟩
  · rintro ⟨hzero, hpos, hproper⟩
    refine ⟨hpos, ?_⟩
    intro J hJ
    by_cases hn : none ∈ J
    · have hmissing : ∃ x ∈ A, some x ∉ J := by
        by_contra h
        push Not at h
        have hfull : indices A ⊆ J := by
          intro i hi
          cases i with
          | none => exact hn
          | some x => exact h x (by simpa [indices] using hi)
        exact hJ.ne (Subset.antisymm hJ.subset hfull)
      obtain ⟨x, hxA, hxJ⟩ := hmissing
      have hsub : J ⊆ indices (A.erase x) := by
        intro i hi
        cases i with
        | none => simp [indices]
        | some y =>
          have hy : y ∈ A := by simpa [indices] using hJ.subset hi
          have hyx : y ≠ x := fun heq ↦ hxJ (heq ▸ hi)
          simp [indices, hyx, hy]
      have hmono := relativeNullityOn_mono (augmented W S) hsub
      have hz := hproper (A.erase x) (erase_ssubset hxA)
      change relativeNullityOn (augmented W S) (indices (A.erase x)) = 0 at hz
      omega
    · have hsub : J ⊆ A.image some := by
        intro i hi
        have hiA := hJ.subset hi
        rcases mem_insert.mp hiA with heq | hmem
        · exact False.elim (hn (heq ▸ hi))
        · exact hmem
      have hmono := relativeNullityOn_mono (augmented W S) hsub
      rw [nullity_some_image W S A, hzero] at hmono
      omega

end PaperP1.PrimitiveCompressionCriterion
