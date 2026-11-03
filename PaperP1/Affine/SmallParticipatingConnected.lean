module

public import PaperP1.Affine.TripleFullSupportConnected
public import PaperP1.Affine.Subfamilies
public import PaperP1.Algebra.SubspaceFamilyRank

/-! # Coordinatewise participation suffices for connectedness at order at most three -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallParticipatingConnected

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank

theorem coordinate_relation {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]
    (S : κ → Submodule 𝔽₂ U) (I : Finset κ) {x : κ} (hx : x ∈ I)
    (hcross : S x ⊓ span S (I.erase x) ≠ ⊥) :
    ∃ s : (i : I) → S i.val, relationAddition (fun i : I ↦ S i.val) s = 0 ∧ s ⟨x, hx⟩ ≠ 0 := by
  classical
  obtain ⟨v, hv, hvn⟩ := (Submodule.ne_bot_iff _).mp hcross
  have hvrange : v ∈ LinearMap.range (relationAddition (fun i : I.erase x ↦ S i.val)) := by
    rw [range_relationAddition]
    exact hv.2
  obtain ⟨u, hu⟩ := hvrange
  let r := subfamilyExtend S (erase_subset x I) u
  let i : I := ⟨x, hx⟩
  let t : (j : I) → S j.val := Pi.single i ⟨v, hv.1⟩
  have hr : relationAddition (fun i : I ↦ S i.val) r = v :=
    (relationAddition_subfamilyExtend S (erase_subset x I) u).trans hu
  have ht : relationAddition (fun i : I ↦ S i.val) t = v := by
    change (∑ j : I, (t j).val) = v
    rw [sum_eq_single i]
    · simp [t]
    · intro j _hj hji
      have htj : t j = 0 := by simp [t, hji]
      rw [htj]
      rfl
    · intro hi
      exact False.elim (hi (mem_univ i))
  have hri : r i = 0 := by simp [r, i, subfamilyExtend]
  have hti : t i = ⟨v, hv.1⟩ := by simp [t]
  refine ⟨r - t, by rw [map_sub, hr, ht, sub_self], ?_⟩
  intro hzero
  have h := congrArg Subtype.val hzero
  change ((r i - t i : S i.val) : U) = 0 at h
  rw [hri, hti] at h
  exact hvn (by simpa using h)

theorem connected {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (S : ι → Submodule 𝔽₂ U) (hcard : Fintype.card ι ≤ 3)
    (hparticipates : ∀ i, ∃ s : (j : ι) → S j, relationAddition S s = 0 ∧ s i ≠ 0) :
    canonicalRelationPartition S = ⊤ := by
  classical
  apply SmallFinpartition.eq_top_without_singletons univ_nonempty (by simpa only [card_univ] using hcard)
  intro C hC hcard
  obtain ⟨i, rfl⟩ := card_eq_one.mp hcard
  obtain ⟨s, hs, hsi⟩ := hparticipates i
  have hzero := canonicalRelationPartition_respects S s hs {i} hC
  rw [sum_singleton] at hzero
  exact hsi (Subtype.ext hzero)

end PaperP1.SmallParticipatingConnected
