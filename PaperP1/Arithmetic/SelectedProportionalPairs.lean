module

public import PaperP1.Arithmetic.EvenIndependentValues
public import PaperP1.Arithmetic.TwoPointSquareClasses

/-! # Two proportional pairs are impossible on the actual selected even-independent value sets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedProportionalPairs

open Finset PaperP1.Arithmetic PaperP1.FiniteEvenSquareClasses

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem pair_mem_space (S : Finset ℕ) (a b : ℕ) (ha : a ∈ S) (hb : b ∈ S) :
    parityVec a + parityVec b ∈ space S := by
  rw [space_eq_span S b hb]
  have hh : parityVec a - parityVec b ∈
      Submodule.span F₂ ((fun n ↦ parityVec n - parityVec b) '' (S : Set ℕ)) :=
    Submodule.subset_span ⟨a, ha, rfl⟩
  simpa only [sub_eq_add_neg, TwoPointSquareClasses.binary_neg_eq_self] using hh

theorem pair_ne_zero (S : Finset ℕ) (hS : EvenIndependentValues.Independent S)
    (a b : ℕ) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) : parityVec a + parityVec b ≠ 0 := by
  have hsubset : ({a, b} : Finset ℕ) ⊆ S := by
    intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact ha
    · exact hb
  have hparity := (EvenIndependentValues.pair_iff a b hab).mp (hS.mono hsubset)
  intro hzero
  have heq := eq_neg_of_add_eq_zero_left hzero
  rw [TwoPointSquareClasses.binary_neg_eq_self] at heq
  exact hparity heq

theorem no_proportional_pairs (S T : Finset ℕ) (hS : EvenIndependentValues.Independent S)
    (hdirect : Disjoint (space S) (space T))
    (hposS : ∀ n ∈ S, 0 < n) (hposT : ∀ n ∈ T, 0 < n)
    (a b c d : ℕ) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ T) (hd : d ∈ T) (hab : a ≠ b) :
    a * d ≠ b * c := by
  intro hcross
  have heq := TwoPointSquareClasses.parity_pair_eq_of_cross_product
    (hposS a ha).ne' (hposS b hb).ne' (hposT c hc).ne' (hposT d hd).ne' hcross
  have hmemS := pair_mem_space S a b ha hb
  have hmemT := pair_mem_space T c d hc hd
  rw [← heq] at hmemT
  exact pair_ne_zero S hS a b ha hb hab ((Submodule.disjoint_def.mp hdirect) _ hmemS hmemT)

def values (x : ℤ) (I : Finset ℤ) : Finset ℕ := I.image fun i ↦ (x + i).natAbs

theorem value_cast (x i : ℤ) (hpos : 0 < x + i) :
    ((x + i).natAbs : ℚ) = (x : ℚ) + (i : ℚ) := by
  rw [Nat.cast_natAbs, abs_of_pos hpos, Int.cast_add]

theorem values_pos (x : ℤ) (I : Finset ℤ) (hpos : ∀ i ∈ I, 0 < x + i) :
    ∀ n ∈ values x I, 0 < n := by
  intro n hn
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
  exact Int.natAbs_pos.mpr (hpos i hi).ne'

theorem values_ne (x a b : ℤ) (ha : 0 < x + a) (hb : 0 < x + b) (hab : a ≠ b) :
    (x + a).natAbs ≠ (x + b).natAbs := by
  intro hh
  have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) hh
  simp only [Int.natCast_natAbs, abs_of_pos ha, abs_of_pos hb] at hcast
  exact hab (add_left_cancel hcast)

end PaperP1.SelectedProportionalPairs
