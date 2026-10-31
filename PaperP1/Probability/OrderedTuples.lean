module

public import PaperP1.Probability.FiniteCoupling
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Fin.Embedding

/-! # Ordered distinct tuples and deletion of one marked coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Probability

open Finset

variable {ι : Type*} [DecidableEq ι]

abbrev OrderedTuple (G : Finset ι) (r : ℕ) := Fin r ↪ G

def tupleValues {G : Finset ι} {r : ℕ} (t : OrderedTuple G r) : Finset ι :=
  univ.image (fun i ↦ (t i).val)

theorem mem_tupleValues {G : Finset ι} {r : ℕ} (t : OrderedTuple G r) (x : ι) :
    x ∈ tupleValues t ↔ ∃ i, (t i).val = x := by
  simp only [tupleValues, mem_image, mem_univ, true_and]

theorem tupleValues_subset {G : Finset ι} {r : ℕ} (t : OrderedTuple G r) : tupleValues t ⊆ G := by
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_tupleValues t x).mp hx
  exact (t i).property

theorem tupleValues_card {G : Finset ι} {r : ℕ} (t : OrderedTuple G r) :
    (tupleValues t).card = r := by
  have hinj : Function.Injective (fun i : Fin r ↦ (t i).val) :=
    Subtype.val_injective.comp t.injective
  rw [tupleValues, card_image_of_injective _ hinj]
  simp

theorem tupleValues_forall {G : Finset ι} {r : ℕ} (t : OrderedTuple G r) (P : ι → Prop) :
    (∀ x ∈ tupleValues t, P x) ↔ ∀ i, P (t i).val := by
  constructor
  · intro h i
    exact h _ ((mem_tupleValues t _).mpr ⟨i, rfl⟩)
  · intro h x hx
    obtain ⟨i, rfl⟩ := (mem_tupleValues t x).mp hx
    exact h i

theorem sum_tupleValues {M : Type*} [AddCommMonoid M] {G : Finset ι} {r : ℕ}
    (t : OrderedTuple G r) (f : ι → M) :
    (∑ x ∈ tupleValues t, f x) = ∑ i, f (t i).val := by
  have hinj : Function.Injective (fun i : Fin r ↦ (t i).val) :=
    Subtype.val_injective.comp t.injective
  exact sum_image hinj.injOn

def eraseTuple {G : Finset ι} {r : ℕ} (t : OrderedTuple G (r + 1)) (i : Fin (r + 1)) :
    OrderedTuple G r := i.succAboveEmb.trans t

theorem tupleValues_erase {G : Finset ι} {r : ℕ}
    (t : OrderedTuple G (r + 1)) (i : Fin (r + 1)) :
    tupleValues (eraseTuple t i) = (tupleValues t).erase (t i).val := by
  ext x
  rw [mem_tupleValues, mem_erase, mem_tupleValues]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨?_, i.succAbove j, hj⟩
    intro hxeq
    have ht : t (i.succAbove j) = t i := Subtype.ext (hj.trans hxeq)
    exact Fin.succAbove_ne i j (t.injective ht)
  · rintro ⟨hne, k, hk⟩
    have hki : k ≠ i := by intro heq; subst k; exact hne hk.symm
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hki
    refine ⟨j, ?_⟩
    change (t (i.succAbove j)).val = x
    rw [hj]
    exact hk

omit [DecidableEq ι] in
theorem eraseTuple_encoding_injective {G : Finset ι} {r : ℕ} (i : Fin (r + 1)) :
    Function.Injective (fun t : OrderedTuple G (r + 1) ↦ (t i, eraseTuple t i)) := by
  intro t u heq
  apply Function.Embedding.ext
  intro k
  by_cases hki : k = i
  · subst k
    exact congrArg Prod.fst heq
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hki
    have h := congrArg (fun v : OrderedTuple G r ↦ v j) (congrArg Prod.snd heq)
    change t (i.succAbove j) = u (i.succAbove j) at h
    simpa only [hj] using h

theorem sum_erased_tuple_bound {G : Finset ι} {r : ℕ}
    (q : Finset ι → ℝ) (hq : ∀ A, 0 ≤ q A)
    (A : Finset (OrderedTuple G (r + 1))) (i : Fin (r + 1)) :
    (∑ t ∈ A, q (tupleValues (eraseTuple t i))) ≤
      (G.card : ℝ) * ∑ s : OrderedTuple G r, q (tupleValues s) := by
  classical
  let enc : OrderedTuple G (r + 1) → G × OrderedTuple G r := fun t ↦ (t i, eraseTuple t i)
  have hinj : Function.Injective enc := eraseTuple_encoding_injective i
  calc
    _ = ∑ v ∈ A.image enc, q (tupleValues v.2) := (sum_image hinj.injOn).symm
    _ ≤ ∑ v : G × OrderedTuple G r, q (tupleValues v.2) := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro v _ _
      exact hq _
    _ = _ := by simp only [Fintype.sum_prod_type, sum_const, card_univ, Fintype.card_coe,
      nsmul_eq_mul]

end PaperP1.Probability
