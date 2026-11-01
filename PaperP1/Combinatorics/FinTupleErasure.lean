module

public import PaperP1.Combinatorics.FiniteCoverCount
public import Mathlib.Data.Fin.Tuple.Basic

/-! # Actual one- and two-coordinate tuple fibres after erasing coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinTupleErasure

open Finset

theorem determined {α : Type*} {r : ℕ} (i : Fin (r + 1)) (n m : Fin (r + 1) → α)
    (hi : n i = m i) (hrest : i.removeNth n = i.removeNth m) : n = m := by
  calc
    n = Fin.insertNth i (n i) (i.removeNth n) := (Fin.insertNth_self_removeNth i n).symm
    _ = Fin.insertNth i (m i) (i.removeNth m) := by rw [hi, hrest]
    _ = m := Fin.insertNth_self_removeNth i m

theorem fixed_coordinate_count {α : Type*} [DecidableEq α] {r : ℕ}
    (S : Finset (Fin (r + 1) → α)) (i : Fin (r + 1)) (x : α) (R : Finset (Fin r → α))
    (hR : ∀ n ∈ S, n i = x → i.removeNth n ∈ R) :
    (S.filter fun n ↦ n i = x).card ≤ R.card := by
  classical
  have hinj : Set.InjOn (fun n : Fin (r + 1) → α ↦ i.removeNth n) (S.filter fun n ↦ n i = x) := by
    intro n hn m hm heq
    exact determined i n m ((mem_filter.mp hn).2.trans (mem_filter.mp hm).2.symm) heq
  rw [← card_image_of_injOn hinj]
  apply card_le_card
  intro n hn
  obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
  exact hR m (mem_filter.mp hm).1 (mem_filter.mp hm).2

theorem pair_determined {α : Type*} {r : ℕ} (i : Fin (r + 2)) (j : Fin (r + 1))
    (n m : Fin (r + 2) → α) (hi : n i = m i) (hj : n (i.succAbove j) = m (i.succAbove j))
    (hrest : j.removeNth (i.removeNth n) = j.removeNth (i.removeNth m)) : n = m := by
  apply determined i n m hi
  exact determined j (i.removeNth n) (i.removeNth m) hj hrest

theorem fixed_pair_count {α : Type*} [DecidableEq α] {r : ℕ}
    (S : Finset (Fin (r + 2) → α)) (i : Fin (r + 2)) (j : Fin (r + 1)) (x y : α)
    (R : Finset (Fin r → α))
    (hR : ∀ n ∈ S, n i = x → n (i.succAbove j) = y → j.removeNth (i.removeNth n) ∈ R) :
    (S.filter fun n ↦ n i = x ∧ n (i.succAbove j) = y).card ≤ R.card := by
  classical
  have hinj : Set.InjOn (fun n : Fin (r + 2) → α ↦ j.removeNth (i.removeNth n))
      (S.filter fun n ↦ n i = x ∧ n (i.succAbove j) = y) := by
    intro n hn m hm heq
    exact pair_determined i j n m ((mem_filter.mp hn).2.1.trans (mem_filter.mp hm).2.1.symm)
      ((mem_filter.mp hn).2.2.trans (mem_filter.mp hm).2.2.symm) heq
  rw [← card_image_of_injOn hinj]
  apply card_le_card
  intro n hn
  obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
  exact hR m (mem_filter.mp hm).1 (mem_filter.mp hm).2.1 (mem_filter.mp hm).2.2

end PaperP1.FinTupleErasure
