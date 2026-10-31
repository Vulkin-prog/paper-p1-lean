module

public import PaperP1.Combinatorics.MatchingCollapse
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Unordered decompositions into two distinct labels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairDecompositions

open Finset

variable {U W : Type*} [AddCommGroup U] [DecidableEq U] [AddCommGroup W] [DecidableEq W]

def pairs (S : Finset U) (α : U) : Finset (Finset U) :=
  S.powersetCard 2 |>.filter fun A ↦ ∑ a ∈ A, a = α

theorem mem_pairs {S A : Finset U} {α : U} :
    A ∈ pairs S α ↔ A ⊆ S ∧ A.card = 2 ∧ (∑ a ∈ A, a) = α := by
  simp only [pairs, mem_filter, mem_powersetCard, and_assoc]

theorem pair_partner {A : Finset U} {α a : U} (hcard : A.card = 2)
    (hsum : (∑ x ∈ A, x) = α) (ha : a ∈ A) :
    ∃ b, a ≠ b ∧ A = {a, b} ∧ a + b = α := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hcard
  simp only [mem_insert, mem_singleton] at ha
  have hsum' : x + y = α := by simpa only [sum_pair hxy, id_eq] using hsum
  rcases ha with rfl | rfl
  · exact ⟨y, hxy, rfl, hsum'⟩
  · exact ⟨x, hxy.symm, pair_comm _ _, (add_comm _ _).trans hsum'⟩

theorem pairs_pairwise_disjoint (S : Finset U) (α : U) :
    ∀ A ∈ pairs S α, ∀ B ∈ pairs S α, A ≠ B → Disjoint A B := by
  intro A hA B hB hne
  apply disjoint_left.mpr
  intro a haA haB
  obtain ⟨_, hcardA, hsumA⟩ := mem_pairs.mp hA
  obtain ⟨_, hcardB, hsumB⟩ := mem_pairs.mp hB
  obtain ⟨b, _, hAb, hab⟩ := pair_partner hcardA hsumA haA
  obtain ⟨c, _, hBc, hac⟩ := pair_partner hcardB hsumB haB
  have hbc : b = c := add_left_cancel (hab.trans hac.symm)
  exact hne (hAb.trans (hbc ▸ hBc.symm))

theorem target_not_mem_pair {S A : Finset U} {α : U} (hzero : (0 : U) ∉ S)
    (hA : A ∈ pairs S α) : α ∉ A := by
  intro hαA
  obtain ⟨hAS, hcard, hsum⟩ := mem_pairs.mp hA
  obtain ⟨b, _, hAb, hab⟩ := pair_partner hcard hsum hαA
  have hb : b = 0 := add_left_cancel (hab.trans (add_zero α).symm)
  apply hzero
  apply hAS
  rw [hAb, ← hb]
  simp

omit [DecidableEq W] in
theorem map_constant_on_pairs (S : Finset U) (α : U) (f : U →+ W)
    (hf : f α = 0) (hneg : ∀ w : W, -w = w) :
    ∀ A ∈ pairs S α, ∀ a ∈ A, ∀ b ∈ A, f a = f b := by
  intro A hA a ha b hb
  by_cases hab : a = b
  · rw [hab]
  obtain ⟨_, hcard, hsum⟩ := mem_pairs.mp hA
  obtain ⟨c, hac, hAc, hsum'⟩ := pair_partner hcard hsum ha
  have hbc : b = c := by
    rw [hAc] at hb
    have hba := (mem_insert.mp hb).resolve_left (Ne.symm hab)
    exact mem_singleton.mp hba
  have hmap : f a + f b = 0 := by
    rw [hbc, ← map_add, hsum', hf]
  have h := eq_neg_of_add_eq_zero_left hmap
  exact h.trans (hneg _)

theorem nonzero_image_card_drop (S : Finset U) (α : U) (f : U →+ W)
    (hS : (0 : U) ∉ S) (hα : α ∈ S) (hf : f α = 0) (hneg : ∀ w : W, -w = w) :
    ((S.image f).erase 0).card + (pairs S α).card + 1 ≤ S.card := by
  apply MatchingCollapse.image_erase_zero_card_bound S (pairs S α) α f hα hf
  · intro A hA
    obtain ⟨hAS, hcard, _⟩ := mem_pairs.mp hA
    exact ⟨hAS, hcard, target_not_mem_pair hS hA⟩
  · exact pairs_pairwise_disjoint S α
  · exact map_constant_on_pairs S α f hf hneg

end PaperP1.PairDecompositions
