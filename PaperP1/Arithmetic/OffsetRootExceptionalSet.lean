module

public import PaperP1.Arithmetic.OffsetRootSeparation

/-! # At most two physical offset coordinates account for all root collisions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetRootExceptionalSet

open Finset PaperP1.Arithmetic PaperP1.OffsetRootSeparation

abbrev Coordinate (L : ℕ) := Fin (L + 1) ⊕ Fin (L + 1)

def root {L : ℕ} (α β : ℚ) : Coordinate L → ℚ := Sum.elim leftRoot (rightRoot α β)

theorem exists_exceptional_coordinates (x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hinj : Function.Injective (evenSquareClassMap x L))
    (hdirect : Disjoint (squareClassSpace x L) (squareClassSpace y L))
    (α β : ℚ) (hα : α ≠ 0) (hline : (y : ℚ) = α * (x : ℚ) + β) :
    ∃ H : Finset (Coordinate L), H.card ≤ 2 ∧ Set.InjOn (root α β) {v | v ∉ H} := by
  by_cases hmatch : ∃ u v : Fin (L + 1), leftRoot u = rightRoot α β v
  · obtain ⟨u₀, v₀, hroot₀⟩ := hmatch
    let H : Finset (Coordinate L) := {Sum.inl u₀, Sum.inr v₀}
    refine ⟨H, by simp [H], ?_⟩
    intro a ha b hb heq
    cases a with
    | inl u =>
      cases b with
      | inl v => exact congrArg Sum.inl (leftRoot_injective L heq)
      | inr v =>
        have hu := match_left_unique x y L hx hy hinj hdirect α β hα hline u v u₀ v₀ heq hroot₀
        have hbad : Sum.inl u ∈ H := by simp only [H, mem_insert, mem_singleton]; exact Or.inl (congrArg Sum.inl hu)
        exact (ha hbad).elim
    | inr v =>
      cases b with
      | inl u =>
        have hu := match_left_unique x y L hx hy hinj hdirect α β hα hline u v u₀ v₀ heq.symm hroot₀
        have hbad : Sum.inl u ∈ H := by simp only [H, mem_insert, mem_singleton]; exact Or.inl (congrArg Sum.inl hu)
        exact (hb hbad).elim
      | inr w => exact congrArg Sum.inr (rightRoot_injective L α β hα heq)
  · refine ⟨∅, by simp, ?_⟩
    intro a _ b _ heq
    cases a with
    | inl u =>
      cases b with
      | inl v => exact congrArg Sum.inl (leftRoot_injective L heq)
      | inr v => exact (hmatch ⟨u, v, heq⟩).elim
    | inr v =>
      cases b with
      | inl u => exact (hmatch ⟨u, v, heq.symm⟩).elim
      | inr w => exact congrArg Sum.inr (rightRoot_injective L α β hα heq)

end PaperP1.OffsetRootExceptionalSet
