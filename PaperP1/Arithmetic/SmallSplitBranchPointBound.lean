module

public import PaperP1.Arithmetic.QuadraticCharacterTwoFactorSum
public import PaperP1.Analysis.SquareRootPointErrorThreshold

/-! # Unconditional leading-coefficient-one source counts when one branch union has at most two elements

Distinctness after coefficient reduction is explicit. No general character-sum
or geometric point estimate is a hypothesis in these theorems.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallSplitBranchPointBound

open Finset SplitRadicalFiniteFieldPointCount
open scoped Classical

theorem union_nonempty_or {ι : Type*} (I J : ι → Finset ℤ) (s : Finset ι) (hs : s.Nonempty)
    (hne : ∀ i ∈ s, (I i).Nonempty ∨ (J i).Nonempty) :
    (s.biUnion I).Nonempty ∨ (s.biUnion J).Nonempty := by
  obtain ⟨i, hi⟩ := hs
  rcases hne i hi with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact Or.inl ⟨a, mem_biUnion.mpr ⟨i, hi, ha⟩⟩
  · exact Or.inr ⟨b, mem_biUnion.mpr ⟨i, hi, hb⟩⟩

theorem small_branch_abs_bound {F : Type*} [Field F] [Fintype F]
    (hodd : ringChar F ≠ 2) (S : Finset ℤ) (hS : S.Nonempty) (hcard : S.card ≤ 2)
    (hinj : Set.InjOn (Int.cast : ℤ → F) (S : Set ℤ)) :
    |((∑ x : F, quadraticChar F (linearValue F S x) : ℤ) : ℝ)| ≤ 1 := by
  by_cases hone : S.card = 1
  · obtain ⟨a, rfl⟩ := card_eq_one.mp hone
    rw [QuadraticCharacterLinearSum.singleton_sum_zero hodd a, Int.cast_zero, abs_zero]
    norm_num
  · have htwo : S.card = 2 := by have := hS.card_pos; omega
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp htwo
    have hcast : (a : F) ≠ (b : F) := by
      intro h
      exact hab (hinj (mem_insert_self _ _) (mem_insert_of_mem (mem_singleton_self _)) h)
    rw [QuadraticCharacterTwoFactorSum.two_shift_sum hodd a b hcast]
    norm_num

theorem error_bound {F ι : Type*} [Field F] [Fintype F] [Fintype ι]
    (hodd : ringChar F ≠ 2) (c : ι → F) (I J : ι → Finset ℤ)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
    (hsmall : ∀ s ∈ (univ : Finset ι).powerset.erase ∅,
      ((s.biUnion I).Nonempty ∧ (s.biUnion I).card ≤ 2 ∧
        Set.InjOn (Int.cast : ℤ → F) (s.biUnion I : Set ℤ)) ∨
      ((s.biUnion J).Nonempty ∧ (s.biUnion J).card ≤ 2 ∧
        Set.InjOn (Int.cast : ℤ → F) (s.biUnion J : Set ℤ))) :
    |((points c I J).card : ℝ) - (Fintype.card F : ℝ) ^ 2| ≤
      ((2 ^ Fintype.card ι - 1 : ℕ) : ℝ) * Fintype.card F := by
  have hc : ((univ : Finset ι).powerset.erase ∅).card = 2 ^ Fintype.card ι - 1 := by
    rw [card_erase_of_mem (empty_mem_powerset (s := univ)), card_powerset, card_univ]
  have hb := SeparatedQuadraticPointError.error_bound hodd c
    (fun i ↦ linearValue F (I i)) (fun i ↦ linearValue F (J i)) 1 (by positivity) (by
      intro s hs
      rw [character_sum_union I s (fun i _ j _ hij ↦ hI hij),
        character_sum_union J s (fun i _ j _ hij ↦ hJ hij)]
      rcases hsmall s hs with ⟨hne, hcard, hinj⟩ | ⟨hne, hcard, hinj⟩
      · exact Or.inl (small_branch_abs_bound hodd _ hne hcard hinj)
      · exact Or.inr (small_branch_abs_bound hodd _ hne hcard hinj))
  rw [hc, mul_one] at hb
  exact hb

theorem uniform_upper_bound {ι : Type*} [Fintype ι] (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (F : Type) [Field F] [Fintype F], K ≤ Fintype.card F → ringChar F ≠ 2 →
      ∀ (c : ι → F) (I J : ι → Finset ℤ),
        (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
        (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
        (∀ s ∈ (univ : Finset ι).powerset.erase ∅,
          ((s.biUnion I).Nonempty ∧ (s.biUnion I).card ≤ 2 ∧
            Set.InjOn (Int.cast : ℤ → F) (s.biUnion I : Set ℤ)) ∨
          ((s.biUnion J).Nonempty ∧ (s.biUnion J).card ≤ 2 ∧
            Set.InjOn (Int.cast : ℤ → F) (s.biUnion J : Set ℤ))) →
        ((points c I J).card : ℝ) ≤ (1 + η) * (Fintype.card F : ℝ) ^ 2 := by
  obtain ⟨K, hK⟩ := SquareRootPointErrorThreshold.exists_threshold
    0 ((2 ^ Fintype.card ι - 1 : ℕ) : ℝ) η (by positivity) (Nat.cast_nonneg _) hη
  refine ⟨K, ?_⟩
  intro F _ _ hlarge hodd c I J hI hJ hsmall
  have he := error_bound hodd c I J hI hJ hsmall
  have ht := hK (Fintype.card F) hlarge
  have hl := le_abs_self (((points c I J).card : ℝ) - (Fintype.card F : ℝ) ^ 2)
  nlinarith only [he, ht, hl]

end PaperP1.SmallSplitBranchPointBound
