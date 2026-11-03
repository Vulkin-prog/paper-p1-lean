module

public import PaperP1.Affine.MinimalRelativeRelations

/-! # A minimal intersection with an old span retains a nonzero source component -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MinimalSpanCrossing

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq ι]

omit [DecidableEq ι] in
theorem exists_minimal (S : ι → Submodule 𝔽₂ U) (W : Submodule 𝔽₂ U)
    (I : Finset ι) (hcross : W ⊓ span S I ≠ ⊥) :
    ∃ A ⊆ I, A.Nonempty ∧ W ⊓ span S A ≠ ⊥ ∧
      ∀ B : Finset ι, B ⊂ A → Disjoint W (span S B) := by
  classical
  let P := I.powerset.filter fun A ↦ W ⊓ span S A ≠ ⊥
  have hIP : I ∈ P := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hcross⟩
  obtain ⟨A, hAP, hmin⟩ := exists_min_image P Finset.card ⟨I, hIP⟩
  obtain ⟨hAI, hA⟩ := mem_filter.mp hAP
  have hsub : A ⊆ I := mem_powerset.mp hAI
  have hne : A.Nonempty := by
    by_contra h
    have heq : A = ∅ := not_nonempty_iff_eq_empty.mp h
    rw [heq, span_empty, inf_bot_eq] at hA
    exact hA rfl
  refine ⟨A, hsub, hne, hA, ?_⟩
  intro B hBA
  apply disjoint_iff.mpr
  by_contra hn
  have hBP : B ∈ P := mem_filter.mpr ⟨mem_powerset.mpr (hBA.subset.trans hsub), hn⟩
  have hle := hmin B hBP
  have hlt := card_lt_card hBA
  omega

theorem exists_relation (S : ι → Submodule 𝔽₂ U) (W : Submodule 𝔽₂ U)
    (A : Finset ι) (hcross : W ⊓ span S A ≠ ⊥)
    (hproper : ∀ B : Finset ι, B ⊂ A → Disjoint W (span S B)) :
    ∃ u : (i : A) → S i.val, (∀ i, u i ≠ 0) ∧
      (∑ i : A, (u i).val) ∈ W ∧ (∑ i : A, (u i).val) ≠ 0 := by
  classical
  obtain ⟨w, hw, hwn⟩ := (Submodule.ne_bot_iff (W ⊓ span S A)).mp hcross
  have hspan : w ∈ LinearMap.range (relationAddition (fun i : A ↦ S i.val)) := by
    rw [range_relationAddition]
    exact hw.2
  obtain ⟨u, hu⟩ := hspan
  change (∑ i : A, (u i).val) = w at hu
  refine ⟨u, ?_, ?_, ?_⟩
  · intro i hz
    have hwrest : w ∈ span S (A.erase i.val) := by
      rw [← hu]
      change (∑ j : A, (u j).val) ∈ span S (A.erase i.val)
      apply Submodule.sum_mem
      intro j _
      by_cases hji : j = i
      · subst j
        simp only [hz, ZeroMemClass.coe_zero]
        exact Submodule.zero_mem _
      · exact local_le_span S _ (mem_erase.mpr
          ⟨fun h ↦ hji (Subtype.ext h), j.property⟩) (u j).property
    have hb : w ∈ W ⊓ span S (A.erase i.val) := ⟨hw.1, hwrest⟩
    rw [(hproper _ (erase_ssubset i.property)).eq_bot] at hb
    exact hwn hb
  · rw [hu]
    exact hw.1
  · rw [hu]
    exact hwn

omit [DecidableEq ι] in
theorem disjoint_singletons (S : ι → Submodule 𝔽₂ U) (W : Submodule 𝔽₂ U)
    (A : Finset ι) (hsize : 2 ≤ A.card)
    (hproper : ∀ B : Finset ι, B ⊂ A → Disjoint W (span S B)) :
    ∀ i ∈ A, Disjoint W (S i) := by
  classical
  intro i hi
  have hsingle : ({i} : Finset ι) ⊂ A := by
    apply ssubset_iff_subset_ne.mpr
    refine ⟨singleton_subset_iff.mpr hi, ?_⟩
    intro heq
    have hc := congrArg Finset.card heq
    simp only [card_singleton] at hc
    omega
  have hspan : span S {i} = S i := by simp [span]
  simpa only [hspan] using hproper {i} hsingle

end PaperP1.MinimalSpanCrossing
