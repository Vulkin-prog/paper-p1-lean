module

public import PaperP1.Asymptotics.CriticalFiniteRungeIndependence
public import PaperP1.Arithmetic.ActualOffsetNonalignment
public import PaperP1.Arithmetic.NormalizedWindowSets

/-! # Uniform two-point independence for every actual critical window

This includes rank-defective windows. Full even-map injectivity is not required.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalTwoPointClasses

open Finset PaperP1.Arithmetic PaperP1.Affine

theorem uniform_nonzero (C : ℝ) : ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x : ℕ, N ≤ x →
    ∀ u v : Fin (L + 1), u ≠ v →
      parityVec (startCompleteVertexLabel x L u) + parityVec (startCompleteVertexLabel x L v) ≠ 0 := by
  obtain ⟨N₀, hN₀, h⟩ := CriticalFiniteRungeIndependence.uniform_independent C 2 1 1 (by omega)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband x hx u v huv hz
  have hxpos : 0 < x := by omega
  have hne : startCompleteVertexLabel x L u ≠ startCompleteVertexLabel x L v :=
    fun he ↦ huv (startCompleteVertexLabel_injective hxpos he)
  have hind := h N hN L hband (x - 1) (L + 1) (by omega) (by omega)
    (by simp) {startCompleteVertexLabel x L u, startCompleteVertexLabel x L v}
    (by rw [card_pair hne]) (by
      intro n hn
      rcases (by simpa only [mem_insert, mem_singleton] using hn :
        n = startCompleteVertexLabel x L u ∨ n = startCompleteVertexLabel x L v) with rfl | rfl
      · rw [startCompleteVertexLabel_eq_offset hxpos]
        exact ⟨by omega, by have hh := u.isLt; omega⟩
      · rw [startCompleteVertexLabel_eq_offset hxpos]
        exact ⟨by omega, by have hh := v.isLt; omega⟩)
  have hp := (EvenIndependentValues.pair_iff _ _ hne).mp hind
  apply hp
  have hneg := eq_neg_of_add_eq_zero_left hz
  simpa only [TwoPointSquareClasses.binary_neg_eq_self] using hneg

theorem uniform_disjoint_no_exact (C : ℝ) : ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x y : ℕ, N ≤ x → N ≤ y →
    Disjoint (squareClassSpace x L) (squareClassSpace y L) →
      ActualOffsetNonalignment.NoExact x y L := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_nonzero C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband x y hx hy hdis
  exact ActualOffsetNonalignment.of_disjoint (by omega) (by omega)
    (h N hN L hband x hx) hdis

end PaperP1.CriticalTwoPointClasses
