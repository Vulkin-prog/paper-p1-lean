module

public import PaperP1.Affine.Relations
public import Mathlib.Data.Fintype.BigOperators

/-! # Full-support relations of two binary spaces are their nonzero common vectors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairFourierIntersection

open Finset PaperP1.Affine

local instance pairFourierPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {U : Type*} [AddCommGroup U] [Module 𝔽₂ U]

instance (priority := 100) intersectionFintype (S T : Submodule 𝔽₂ U) [Fintype S] :
    Fintype ↥(S ⊓ T) :=
  Fintype.ofInjective (fun z : ↥(S ⊓ T) ↦ (⟨z.val, z.property.1⟩ : S))
    (by intro z w h; exact Subtype.ext (congrArg (fun v : S ↦ v.val) h))

theorem self_add (u : U) : u + u = 0 := by
  rw [← two_smul 𝔽₂ u, show (2 : 𝔽₂) = 0 by decide, zero_smul]

theorem add_zero_iff (u v : U) : u + v = 0 ↔ u = v := by
  constructor
  · intro h
    calc
      u = u + (v + v) := by rw [self_add, add_zero]
      _ = (u + v) + v := (add_assoc _ _ _).symm
      _ = v := by rw [h, zero_add]
  · rintro rfl
    exact self_add _

theorem full_relation_iff (S : Bool → Submodule 𝔽₂ U) (s : (i : Bool) → S i) :
    IsFullSupportRelation S s ↔
      (s false).val = (s true).val ∧ (s false).val ≠ 0 := by
  constructor
  · rintro ⟨hs, hsum⟩
    have heq : (s true).val = (s false).val :=
      (add_zero_iff _ _).mp (by simpa only [relationAddition_apply, Fintype.sum_bool] using hsum)
    refine ⟨heq.symm, ?_⟩
    intro hz
    exact hs false (Subtype.ext hz)
  · rintro ⟨heq, hn⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      cases i
      · exact hn (congrArg (fun v : S false ↦ v.val) hi)
      · exact hn (heq.trans (congrArg (fun v : S true ↦ v.val) hi))
    · change (∑ i : Bool, (s i).val) = 0
      rw [Fintype.sum_bool, ← heq, self_add]

def common (S : Bool → Submodule 𝔽₂ U) (s : (i : Bool) → S i)
    (hs : IsFullSupportRelation S s) : ↥(S false ⊓ S true) :=
  ⟨(s false).val, (s false).property,
    ((full_relation_iff S s).mp hs).1 ▸ (s true).property⟩

def diagonal (S : Bool → Submodule 𝔽₂ U) (z : ↥(S false ⊓ S true)) : (i : Bool) → S i
  | false => ⟨z.val, z.property.1⟩
  | true => ⟨z.val, z.property.2⟩

theorem full_support_family_sum {E : Type*} [AddCommMonoid E]
    (S : Bool → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]
    [Fintype ↥(S false ⊓ S true)] (f : U → U → E) :
    (∑ s : (i : Bool) → S i,
      if IsFullSupportRelation S s then f (s false).val (s true).val else 0) =
    ∑ z : ↥(S false ⊓ S true), if z ≠ 0 then f z.val z.val else 0 := by
  classical
  rw [← sum_filter, ← sum_filter]
  refine sum_bij (fun s hs ↦ common S s (mem_filter.mp hs).2) ?_ ?_ ?_ ?_
  · intro s hs
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    intro hz
    exact ((full_relation_iff S s).mp (mem_filter.mp hs).2).2
      (congrArg (fun z : ↥(S false ⊓ S true) ↦ z.val) hz)
  · intro s hs t ht heq
    have hval := congrArg (fun z : ↥(S false ⊓ S true) ↦ z.val) heq
    have hleft : (s false).val = (t false).val := hval
    funext i
    apply Subtype.ext
    cases i
    · exact hleft
    · exact ((full_relation_iff S s).mp (mem_filter.mp hs).2).1.symm.trans
        (hleft.trans ((full_relation_iff S t).mp (mem_filter.mp ht).2).1)
  · intro z hz
    have hn : z.val ≠ 0 := fun h ↦ (mem_filter.mp hz).2 (Subtype.ext h)
    have hd : IsFullSupportRelation S (diagonal S z) :=
      (full_relation_iff S _).mpr ⟨rfl, hn⟩
    exact ⟨diagonal S z, mem_filter.mpr ⟨mem_univ _, hd⟩, Subtype.ext rfl⟩
  · intro s hs
    change f (s false).val (s true).val = f (s false).val (s false).val
    rw [((full_relation_iff S s).mp (mem_filter.mp hs).2).1]

end PaperP1.PairFourierIntersection
