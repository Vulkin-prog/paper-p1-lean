module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # The Veronese algebra as the actual range of the direct sum of multiple-degree pieces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeroneseAlgebra

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
variable (G : ℕ → Submodule F A) [SetLike.GradedMonoid G] (D : ℕ)

theorem multipleGradedMonoid : SetLike.GradedMonoid (fun n ↦ G (n * D)) where
  one_mem := by simpa only [zero_mul] using SetLike.one_mem_graded G
  mul_mem := by
    intro n m x y hx hy
    simpa only [add_mul] using SetLike.mul_mem_graded hx hy

attribute [local instance] multipleGradedMonoid

def veronese : Subalgebra F A := (DirectSum.coeAlgHom (fun n ↦ G (n * D))).range

theorem piece_mem (n : ℕ) {x : A} (hx : x ∈ G (n * D)) : x ∈ veronese G D := by
  exact ⟨DirectSum.of (fun n ↦ G (n * D)) n ⟨x, hx⟩, DirectSum.coeAlgHom_of _ _ _⟩

theorem veronese_eq_adjoin :
    veronese G D = Algebra.adjoin F {x | ∃ n, x ∈ G (n * D)} := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    induction a using DirectSum.induction_on with
    | zero => simpa only [map_zero] using (Algebra.adjoin F {x | ∃ n, x ∈ G (n * D)}).zero_mem
    | of n x =>
      change DirectSum.coeAlgHom (fun n ↦ G (n * D))
        (DirectSum.of (fun n ↦ G (n * D)) n x) ∈ Algebra.adjoin F {x | ∃ n, x ∈ G (n * D)}
      rw [DirectSum.coeAlgHom_of]
      exact Algebra.subset_adjoin ⟨n, x.property⟩
    | add a b ha hb =>
      rw [map_add]
      exact (Algebra.adjoin F {x | ∃ n, x ∈ G (n * D)}).add_mem ha hb
  · apply Algebra.adjoin_le
    rintro x ⟨n, hn⟩
    exact piece_mem G D n hn

theorem veronese_toSubmodule :
    (veronese G D).toSubmodule = ⨆ n, G (n * D) :=
  (Submodule.iSup_eq_toSubmodule_range (fun n ↦ G (n * D))).symm

end PaperP1.GradedVeroneseAlgebra
