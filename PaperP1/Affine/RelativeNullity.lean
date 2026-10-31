module

public import PaperP1.Affine.CenteredFourier

/-!
# Effective relative nullity and full-support relation counts

The nullity is the kernel dimension of addition from the product of the
effective spaces. Rank-nullity identifies it with the manuscript's dimension
deficit. For a nonempty family, full-support relations omit the zero tuple.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace PaperP1.Affine

local instance (P : Prop) : Decidable P := Classical.propDecidable P
local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U]
variable [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

def relativeNullity : ℕ := Module.finrank 𝔽₂ (LinearMap.ker (relationAddition S))

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
theorem range_relationAddition : LinearMap.range (relationAddition S) = ⨆ i, S i := by
  classical
  apply le_antisymm
  · rintro f ⟨s, rfl⟩
    exact Submodule.sum_mem _ (fun i _ => (le_iSup S i) (s i).property)
  · refine iSup_le fun i => ?_
    intro f hf
    refine LinearMap.mem_range.mpr ⟨Pi.single i (⟨f, hf⟩ : S i), ?_⟩
    simp only [relationAddition_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp

omit [DecidableEq ι] in
theorem relativeNullity_eq_dimension_deficit :
    relativeNullity S = (∑ i, Module.finrank 𝔽₂ (S i)) -
      Module.finrank 𝔽₂ (⨆ i, S i : Submodule 𝔽₂ U) := by
  let : ∀ i, Module.Free 𝔽₂ (S i) := fun i => Module.Free.of_divisionRing 𝔽₂ (S i)
  have h := LinearMap.finrank_range_add_finrank_ker
    (K := 𝔽₂) (V := (i : ι) → S i) (V₂ := U) (relationAddition S)
  rw [range_relationAddition, Module.finrank_pi_fintype] at h
  exact Nat.eq_sub_of_add_eq (by simpa [relativeNullity, add_comm] using h)

def fullSupportRelations : Finset ((i : ι) → S i) :=
  Finset.univ.filter (IsFullSupportRelation S)

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
theorem fullSupportRelation_ne_zero [Nonempty ι] (s : (i : ι) → S i)
    (hs : IsFullSupportRelation S s) : s ≠ 0 := by
  intro hz
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact hs.1 i (by rw [hz]; rfl)

theorem fullSupportRelations_subset_erase_zero [Nonempty ι] :
    fullSupportRelations S ⊆
      (Finset.univ.filter fun s => relationAddition S s = 0).erase 0 := by
  intro s hs
  have hp := (Finset.mem_filter.mp hs).2
  exact Finset.mem_erase.mpr ⟨fullSupportRelation_ne_zero S s hp,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩⟩

theorem card_fullSupportRelations_le [Nonempty ι] :
    (fullSupportRelations S).card ≤ 2 ^ relativeNullity S - 1 := by
  classical
  let : AddCommGroup (LinearMap.ker (relationAddition S)) :=
    Submodule.addCommGroup (R := 𝔽₂) (M := (i : ι) → S i) _
  let : Fintype (LinearMap.ker (relationAddition S)) := Fintype.ofFinite _
  have hcard : (Finset.univ.filter fun s => relationAddition S s = 0).card =
      2 ^ relativeNullity S := by
    calc
      _ = Fintype.card (LinearMap.ker (relationAddition S)) := by
        symm
        simpa only [LinearMap.mem_ker] using
          (Fintype.card_subtype (fun s => s ∈ LinearMap.ker (relationAddition S)))
      _ = _ := card_eq_two_pow_finrank (V := LinearMap.ker (relationAddition S))
  calc
    (fullSupportRelations S).card ≤
        ((Finset.univ.filter fun s => relationAddition S s = 0).erase 0).card :=
      Finset.card_le_card (fullSupportRelations_subset_erase_zero S)
    _ = 2 ^ relativeNullity S - 1 := by
      rw [Finset.card_erase_of_mem (by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, map_zero _⟩), hcard]

end PaperP1.Affine
