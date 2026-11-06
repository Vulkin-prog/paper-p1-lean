module

public import PaperP1.Arithmetic.BoundedProductFibres
public import Mathlib.Data.List.Prime
public import Mathlib.Data.List.Permutation
public import Mathlib.Algebra.BigOperators.Fin

/-! # The literal ordered prime-product fibres have at most k-factorial members -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeProductFibres
open Finset
open scoped Classical

theorem tuple_permutation {k : ℕ} (x y : Fin k → ℕ)
    (hx : ∀ i, (x i).Prime) (hy : ∀ i, (y i).Prime)
    (hprod : (∏ i, x i) = ∏ i, y i) : List.Perm (List.ofFn x) (List.ofFn y) := by
  apply perm_of_prod_eq_prod
  · simpa only [List.prod_ofFn] using hprod
  · intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact (hx i).prime
  · intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact (hy i).prime

theorem fibre_card_le_factorial (k : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (((PaperP1.BoundedProductFibres.tuples k P).filter
      (fun x ↦ PaperP1.BoundedProductFibres.value x = n)).card) ≤ k.factorial := by
  let F := (PaperP1.BoundedProductFibres.tuples k P).filter
    (fun x ↦ PaperP1.BoundedProductFibres.value x = n)
  by_cases hF : F.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hF
    have hxprime : ∀ i, (x₀ i).Prime := fun i ↦ hP _ (Fintype.mem_piFinset.mp (mem_filter.mp hx₀).1 i)
    have hcard : F.card ≤ (List.ofFn x₀).permutations.toFinset.card := by
      apply card_le_card_of_injOn List.ofFn
      · intro x hx
        apply List.mem_toFinset.mpr
        apply List.mem_permutations.mpr
        apply tuple_permutation x x₀
        · intro i
          exact hP _ (Fintype.mem_piFinset.mp (mem_filter.mp hx).1 i)
        · exact hxprime
        · exact (mem_filter.mp hx).2.trans (mem_filter.mp hx₀).2.symm
      · intro x hx y hy he
        exact List.ofFn_injective he
    exact hcard.trans (by simpa only [List.length_permutations, List.length_ofFn] using
      List.toFinset_card_le (List.ofFn x₀).permutations)
  · have he : F = ∅ := not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ k.factorial
    rw [he, card_empty]
    exact Nat.zero_le _
end PrimeProductFibres
