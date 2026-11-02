module

public import PaperP1.Arithmetic.BiquadraticWordNorm
public import PaperP1.Arithmetic.BiquadraticRungeMatrix

/-! # The actual finite word sets supply injective branch lists of the exact source ranks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticWordEnumeration

open Finset PaperP1.BiquadraticRungeMatrix
open scoped symmDiff

def enumeration {m : ℕ} (E : Finset ℤ) (hE : E.card = m) : Fin m ≃ E :=
  (Finset.equivFinOfCardEq hE).symm

def list {m : ℕ} (E : Finset ℤ) (hE : E.card = m) (i : Fin m) : ℤ := (enumeration E hE i).val

theorem list_mem {m : ℕ} (E : Finset ℤ) (hE : E.card = m) (i : Fin m) : list E hE i ∈ E :=
  (enumeration E hE i).property

theorem list_injective {m : ℕ} (E : Finset ℤ) (hE : E.card = m) : Function.Injective (list E hE) := by
  intro i j h
  exact (enumeration E hE).injective (Subtype.ext h)

theorem list_product {M : Type*} [CommMonoid M] {m : ℕ} (E : Finset ℤ) (hE : E.card = m) (f : ℤ → M) :
    (∏ i : Fin m, f (list E hE i)) = ∏ u ∈ E, f u := by
  calc
    _ = ∏ u : E, f u.val := Equiv.prod_comp (enumeration E hE) (fun u : E ↦ f u.val)
    _ = _ := Finset.prod_coe_sort E f

def offsets (I K : Finset ℤ) : Fin 4 → Finset ℤ := ![∅, I, K, I ∆ K]

theorem offsets_card (I K : Finset ℤ) (r : Fin 3 → ℕ)
    (hcard : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2) (χ : Fin 4) :
    (offsets I K χ).card = 2 * blockRank r χ := by
  fin_cases χ
  · rfl
  · exact hcard.1
  · exact hcard.2.1
  · exact hcard.2.2

def rootLists (I K : Finset ℤ) (r : Fin 3 → ℕ)
    (hcard : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2) :
    (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ :=
  fun χ ↦ list (offsets I K χ) (offsets_card I K r hcard χ)

theorem offsets_bound (I K : Finset ℤ) (B : ℕ)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hK : ∀ i ∈ K, |i| ≤ (B : ℤ)) :
    ∀ χ : Fin 4, ∀ u ∈ offsets I K χ, |u| ≤ (B : ℤ) := by
  intro χ u hu
  fin_cases χ
  · exact False.elim ((notMem_empty u) hu)
  · exact hI u hu
  · exact hK u hu
  · rcases mem_symmDiff.mp hu with h | h
    · exact hI u h.1
    · exact hK u h.1

theorem rootLists_bound (I K : Finset ℤ) (r : Fin 3 → ℕ)
    (hcard : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2) (B : ℕ)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hK : ∀ i ∈ K, |i| ≤ (B : ℤ)) :
    ∀ χ i, |rootLists I K r hcard χ i| ≤ (B : ℤ) := by
  intro χ i
  exact offsets_bound I K B hI hK χ _ (list_mem _ _ i)

theorem rootLists_product {M : Type*} [CommMonoid M] (I K : Finset ℤ) (r : Fin 3 → ℕ)
    (hcard : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2) (χ : Fin 4) (f : ℤ → M) :
    (∏ i, f (rootLists I K r hcard χ i)) = ∏ u ∈ offsets I K χ, f u :=
  list_product _ _ f

end PaperP1.BiquadraticWordEnumeration
