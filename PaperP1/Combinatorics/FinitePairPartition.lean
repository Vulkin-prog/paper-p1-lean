module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Algebra.Group.Even
public import Lean.Elab.Tactic.Omega

/-! # An actual partition of every even finite set into disjoint pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePairPartition

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem exists_pair_partition (A : Finset ι) (heven : Even A.card) :
    ∃ P : Finset (Finset ι), Set.PairwiseDisjoint (P : Set (Finset ι)) id ∧
      P.biUnion id = A ∧ ∀ B ∈ P, B.card = 2 := by
  classical
  revert heven
  refine Finset.strongInductionOn A ?_
  intro A ih heven
  by_cases hA : A = ∅
  · subst A
    exact ⟨∅, by simp, by simp, by simp⟩
  · obtain ⟨k, hk⟩ := heven
    have hpos : 0 < A.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hA)
    have htwo : 2 ≤ A.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < A.card by omega)
    let R := (A.erase a).erase b
    have hba : b ∈ A.erase a := mem_erase.mpr ⟨hab.symm, hb⟩
    have hRcard : R.card + 2 = A.card := by
      dsimp [R]
      rw [card_erase_of_mem hba, card_erase_of_mem ha]
      omega
    have hRsmall : R ⊂ A := lt_of_le_of_lt (erase_subset b (A.erase a)) (erase_ssubset ha)
    have hReven : Even R.card := ⟨k - 1, by omega⟩
    obtain ⟨P, hdis, hunion, hpairs⟩ := ih R hRsmall hReven
    have hnew : ∀ B ∈ P, Disjoint ({a, b} : Finset ι) B := by
      intro B hB
      apply Finset.disjoint_left.mpr
      intro x hx hxB
      have hxR : x ∈ R := by
        rw [← hunion]
        exact mem_biUnion.mpr ⟨B, hB, hxB⟩
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with hxa | hxb
      · subst x
        simp [R] at hxR
      · subst x
        simp [R] at hxR
    have hdis' : Set.PairwiseDisjoint (insert ({a, b} : Finset ι) (P : Set (Finset ι))) id :=
      hdis.insert (fun B hB _ ↦ hnew B hB)
    refine ⟨insert {a, b} P, ?_, ?_, ?_⟩
    · simpa only [coe_insert] using hdis'
    · rw [biUnion_insert, hunion]
      simp only [id_eq]
      ext x
      by_cases hxa : x = a
      · subst x
        simp [ha]
      · by_cases hxb : x = b
        · subst x
          simp [hb]
        · simp [R, hxa, hxb]
    · intro B hB
      obtain rfl | hBP := mem_insert.mp hB
      · simp [hab]
      · exact hpairs B hBP

theorem partition_cardinality (A : Finset ι) (P : Finset (Finset ι))
    (hdis : Set.PairwiseDisjoint (P : Set (Finset ι)) id) (hunion : P.biUnion id = A)
    (hpairs : ∀ B ∈ P, B.card = 2) : A.card = 2 * P.card := by
  have hsum : (∑ _a ∈ P.biUnion id, (1 : ℕ)) = ∑ B ∈ P, ∑ _a ∈ B, (1 : ℕ) := by
    simpa only [id_eq] using (sum_biUnion (f := fun _ : ι ↦ (1 : ℕ)) hdis)
  have hc : (P.biUnion id).card = ∑ B ∈ P, B.card := by simpa using hsum
  rw [hunion] at hc
  calc
    A.card = ∑ B ∈ P, B.card := hc
    _ = ∑ _B ∈ P, (2 : ℕ) := sum_congr rfl hpairs
    _ = _ := by simp [Nat.mul_comm]

end PaperP1.FinitePairPartition
