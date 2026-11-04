module

public import PaperP1.Affine.MissingBlockRelations

/-! # A single effective source can be inserted or erased from a participating family

The source centre may already occur among the target centres. The alternative
keeps this collision explicit and loses at most one target coordinate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OneSeedParticipation

open Finset PaperP1.Affine

variable {V κ : Type*} [AddCommGroup V] [Module 𝔽₂ V] [DecidableEq κ]

def Witnesses (S : κ → Submodule 𝔽₂ V) (W : Submodule 𝔽₂ V) (I : Finset κ) : Prop :=
  ∀ i : I, ∃ u : (j : I) → S j.val, u i ≠ 0 ∧ (∑ j : I, (u j).val) ∈ W

omit [DecidableEq κ] in
theorem mono (S T : κ → Submodule 𝔽₂ V) (W U : Submodule 𝔽₂ V) (I : Finset κ)
    (hST : ∀ x ∈ I, S x ≤ T x) (hWU : W ≤ U) (h : Witnesses S W I) : Witnesses T U I := by
  intro i
  obtain ⟨u, hu, hsum⟩ := h i
  let v : (j : I) → T j.val := fun j ↦ ⟨(u j).val, hST j.val j.property (u j).property⟩
  refine ⟨v, ?_, hWU hsum⟩
  intro hz
  have hzval := congrArg (fun z : T i.val ↦ (z : V)) hz
  exact hu (Subtype.ext hzval)

theorem coordinate_extension (S : κ → Submodule 𝔽₂ V) (W : Submodule 𝔽₂ V)
    (a : κ) (I : Finset κ) (hW : W ≤ S a) (h : Witnesses S W I)
    (i : I) (hia : i.val ≠ a) :
    ∃ v : (j : (insert a I : Finset κ)) → S j.val,
      relationAddition (fun j : (insert a I : Finset κ) ↦ S j.val) v = 0 ∧
        v ⟨i.val, mem_insert_of_mem i.property⟩ ≠ 0 := by
  classical
  obtain ⟨u, hu, hsum⟩ := h i
  let ia : (insert a I : Finset κ) := ⟨a, mem_insert_self a I⟩
  let t : (j : (insert a I : Finset κ)) → S j.val := Pi.single ia ⟨∑ j : I, (u j).val, hW hsum⟩
  let r := subfamilyExtend S (subset_insert a I) u
  have hr : relationAddition (fun j : (insert a I : Finset κ) ↦ S j.val) r = ∑ j : I, (u j).val :=
    relationAddition_subfamilyExtend S (subset_insert a I) u
  have ht : relationAddition (fun j : (insert a I : Finset κ) ↦ S j.val) t = ∑ j : I, (u j).val := by
    change (∑ j : (insert a I : Finset κ), (t j).val) = _
    rw [sum_eq_single ia]
    · simp [t]
    · intro j _hj hji
      have htj : t j = 0 := by simp [t, hji]
      rw [htj]
      rfl
    · intro hi
      exact False.elim (hi (mem_univ ia))
  refine ⟨r - t, by rw [map_sub, hr, ht, sub_self], ?_⟩
  have hieq : (⟨i.val, mem_insert_of_mem i.property⟩ : (insert a I : Finset κ)) ≠ ia :=
    fun heq ↦ hia (congrArg Subtype.val heq)
  change (r ⟨i.val, mem_insert_of_mem i.property⟩ - t ⟨i.val, mem_insert_of_mem i.property⟩) ≠ 0
  have hri : r ⟨i.val, mem_insert_of_mem i.property⟩ = u i := by
    change (if hi : i.val ∈ I then u ⟨i.val, hi⟩ else (0 : S i.val)) = u i
    rw [dite_eq_left i.property]
  have hti : t ⟨i.val, mem_insert_of_mem i.property⟩ = 0 := by simp [t, hieq]
  rw [hri, hti, sub_zero]
  exact hu

theorem insert_or_erase (S : κ → Submodule 𝔽₂ V) (W : Submodule 𝔽₂ V)
    (a : κ) (I : Finset κ) (hW : W ≤ S a) (h : Witnesses S W I) :
    Witnesses S ⊥ ((insert a I : Finset κ)) ∨ Witnesses S ⊥ (I.erase a) := by
  classical
  let ia : (insert a I : Finset κ) := ⟨a, mem_insert_self a I⟩
  by_cases ha : ∃ v : (j : (insert a I : Finset κ)) → S j.val,
      relationAddition (fun j : (insert a I : Finset κ) ↦ S j.val) v = 0 ∧ v ia ≠ 0
  · left
    intro i
    by_cases hi : i.val = a
    · obtain ⟨v, hv, hne⟩ := ha
      have hieq : i = ia := Subtype.ext hi
      refine ⟨v, hieq.symm ▸ hne, ?_⟩
      simpa only [relationAddition_apply, Submodule.mem_bot] using hv
    · have hiI : i.val ∈ I := (mem_insert.mp i.property).resolve_left hi
      obtain ⟨v, hv, hne⟩ := coordinate_extension S W a I hW h ⟨i.val, hiI⟩ hi
      exact ⟨v, hne, by simpa only [relationAddition_apply, Submodule.mem_bot] using hv⟩
  · right
    intro i
    have hiI := (mem_erase.mp i.property).2
    have hia := (mem_erase.mp i.property).1
    obtain ⟨v, hv, hne⟩ := coordinate_extension S W a I hW h ⟨i.val, hiI⟩ hia
    have hzero : v ia = 0 := by
      by_contra hn
      exact ha ⟨v, hv, hn⟩
    have hsub : I.erase a ⊆ (insert a I : Finset κ) := (erase_subset a I).trans (subset_insert a I)
    obtain ⟨u, hu⟩ := subfamilyExtend_has_preimage S hsub v (by
      intro j hj
      have hja : j.val = a := by
        rcases mem_insert.mp j.property with hja | hjI
        · exact hja
        · by_contra hna
          exact hj (mem_erase.mpr ⟨hna, hjI⟩)
      have heq : j = ia := Subtype.ext hja
      exact heq.symm ▸ hzero)
    refine ⟨u, ?_, ?_⟩
    · intro hui
      have hh := congrFun hu ⟨i.val, hsub i.property⟩
      change (if hi : i.val ∈ I.erase a then u ⟨i.val, hi⟩ else (0 : S i.val)) = v ⟨i.val, hsub i.property⟩ at hh
      rw [dite_eq_left i.property] at hh
      exact hne (hh.symm.trans hui)
    · have hh : relationAddition (fun j : I.erase a ↦ S j.val) u = 0 := by
        rw [← relationAddition_subfamilyExtend S hsub, hu]
        exact hv
      simpa only [relationAddition_apply, Submodule.mem_bot] using hh

end PaperP1.OneSeedParticipation
