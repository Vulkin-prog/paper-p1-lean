module

public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Fintype.EquivFin

/-! # A fixed subsystem with one common positive degree

The subsystem size is fixed before the larger equation count. Its injection
preserves every original disjointness and coefficient condition.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteDegreeSelection

open Finset

theorem select {n K k : ℕ} (hk : 0 < k) (hn : (K + 1) * k ≤ n)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i ∧ d i ≤ K) :
    ∃ a : ℕ, 0 < a ∧ a ≤ K ∧ ∃ f : Fin k → Fin n,
      Function.Injective f ∧ ∀ i, d (f i) = a := by
  classical
  let g : Fin n → Fin (K + 1) := fun i ↦ ⟨d i, by have hh := (hd i).2; omega⟩
  have hpop : Fintype.card (Fin (K + 1)) * k ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using hn
  obtain ⟨a, ha⟩ := Fintype.exists_le_card_fiber_of_mul_le_card g hpop
  obtain ⟨F, hF, hFk⟩ := exists_subset_card_eq ha
  let e : Fin k ≃ F := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hFk)).symm
  let f : Fin k → Fin n := fun i ↦ (e i).val
  have hf : Function.Injective f := fun _ _ hh ↦ e.injective (Subtype.ext hh)
  have he (i : Fin k) : d (f i) = a.val := by
    have hh := (mem_filter.mp (hF (e i).property)).2
    exact congrArg Fin.val hh
  have hpos : 0 < a.val := by rw [← he ⟨0, hk⟩]; exact (hd (f ⟨0, hk⟩)).1
  exact ⟨a.val, hpos, by omega, f, hf, he⟩

end PaperP1.FiniteDegreeSelection
