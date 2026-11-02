module

public import PaperP1.Combinatorics.TuplePositions
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Ring

/-! # Ordered replica occurrences flatten to literal extensions of their first tuple -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReplicaTupleIndex

open Finset

def index (r q : ℕ) : Fin (q + 1) × Fin r ≃ Fin (r + q * r) :=
  finProdFinEquiv.trans (finCongr (by ring))

theorem index_first (r q : ℕ) (i : Fin r) : index r q (0, i) = Fin.castAdd (q * r) i := by
  apply Fin.ext
  change i.val + r * 0 = i.val
  simp

def flatten {r q : ℕ} (t : Fin (q + 1) → Fin r → ℕ) : Fin (r + q * r) → ℕ :=
  fun i ↦ t ((index r q).symm i).1 ((index r q).symm i).2

theorem flatten_apply {r q : ℕ} (t : Fin (q + 1) → Fin r → ℕ) (j : Fin (q + 1)) (i : Fin r) :
    flatten t (index r q (j, i)) = t j i := by
  simp only [flatten, Equiv.symm_apply_apply]

theorem flatten_injective (r q : ℕ) : Function.Injective (@flatten r q) := by
  intro t u h
  funext j i
  have hji := congrFun h (index r q (j, i))
  simpa only [flatten_apply] using hji

theorem initial_flatten {r q : ℕ} (t : Fin (q + 1) → Fin r → ℕ) :
    TupleExtensions.initial (q * r) (flatten t) = t 0 := by
  funext i
  rw [TuplePositions.initial_apply, ← index_first, flatten_apply]

def family {r : ℕ} (A : Finset (Fin r → ℕ)) (q : ℕ) : Finset (Fin (r + q * r) → ℕ) :=
  univ.image (fun t : Fin (q + 1) → A ↦ flatten (fun j ↦ (t j).val))

theorem family_subset_more {r : ℕ} (G : Finset ℕ) (A : Finset (Fin r → ℕ))
    (hA : ∀ x ∈ A, ∀ i, x i ∈ G) (q : ℕ) : family A q ⊆ TupleExtensions.more G A (q * r) := by
  intro y hy
  obtain ⟨t, _, rfl⟩ := mem_image.mp hy
  apply (TupleExtensions.mem_more G A hA (q * r) _).mpr
  constructor
  · simpa only [initial_flatten] using (t 0).property
  · intro i
    exact hA _ (t ((index r q).symm i).1).property ((index r q).symm i).2

theorem subtype_flatten_injective {r : ℕ} (A : Finset (Fin r → ℕ)) (q : ℕ) :
    Function.Injective (fun t : Fin (q + 1) → A ↦ flatten (fun j ↦ (t j).val)) := by
  intro t u h
  have htu := flatten_injective r q h
  funext j
  exact Subtype.ext (congrFun htu j)

end PaperP1.ReplicaTupleIndex
