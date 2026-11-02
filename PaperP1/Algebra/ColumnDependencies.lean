module

public import PaperP1.Algebra.GreedyShortKernel

/-! # Actual short kernel witnesses for zero and repeated columns -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ColumnDependencies

open Finset PaperP1.GreedyShortKernel

variable {K V E : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

theorem zero_column (f : (E →₀ K) →ₗ[K] V) (e : E) (he : f (Finsupp.single e 1) = 0) :
    HasShortVector f {e} 1 := by
  classical
  let x : LinearMap.ker f := ⟨Finsupp.single e 1, he⟩
  refine ⟨x, ?_, ?_, ?_⟩
  · intro h
    have heq := congrArg (fun y : LinearMap.ker f ↦ y.val e) h
    simp [x] at heq
  · change (Finsupp.single e (1 : K)).support ⊆ {e}
    simp
  · change (Finsupp.single e (1 : K)).support.card ≤ 1
    simp

theorem equal_columns [DecidableEq E] (f : (E →₀ K) →ₗ[K] V) (e d : E) (hne : e ≠ d)
    (heq : f (Finsupp.single e 1) = f (Finsupp.single d 1)) : HasShortVector f {e, d} 2 := by
  classical
  let v : E →₀ K := Finsupp.single e 1 - Finsupp.single d 1
  have hv : f v = 0 := by
    change f (Finsupp.single e 1 - Finsupp.single d 1) = 0
    rw [map_sub, heq, sub_self]
  let x : LinearMap.ker f := ⟨v, hv⟩
  have hsupport : v.support ⊆ {e, d} := by
    simpa only [v, Finsupp.support_single e one_ne_zero,
      Finsupp.support_single d one_ne_zero, singleton_union] using
      (Finsupp.support_sub : v.support ⊆ (Finsupp.single e (1 : K)).support ∪ (Finsupp.single d (1 : K)).support)
  refine ⟨x, ?_, hsupport, (card_le_card hsupport).trans card_le_two⟩
  intro h
  have he := congrArg (fun y : LinearMap.ker f ↦ y.val e) h
  simp [x, v, hne.symm] at he

end PaperP1.ColumnDependencies
