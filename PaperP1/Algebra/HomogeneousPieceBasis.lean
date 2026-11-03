module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

/-! # A literal homogeneous basis restricts to a basis of each actual graded piece -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousPieceBasis

open Module DirectSum

variable {F A ι : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G]
  (e : Basis ι F A) (w : ι → ℕ) (he : ∀ i, e i ∈ G (w i))

include he in
theorem piece_eq_span (n : ℕ) :
    G n = Submodule.span F (Set.range fun i : {i : ι // w i = n} ↦ e i) := by
  let T := Submodule.span F (Set.range fun i : {i : ι // w i = n} ↦ e i)
  have hproj : (⊤ : Submodule F A) ≤ T.comap (GradedAlgebra.proj G n) := by
    rw [← e.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change GradedAlgebra.proj G n (e i) ∈ T
    by_cases hi : w i = n
    · have hp : GradedAlgebra.proj G n (e i) = e i := by
        rw [GradedAlgebra.proj_apply]
        exact decompose_of_mem_same G (hi ▸ he i)
      rw [hp]
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · have hp : GradedAlgebra.proj G n (e i) = 0 := by
        rw [GradedAlgebra.proj_apply]
        exact decompose_of_mem_ne G (he i) hi
      rw [hp]
      exact T.zero_mem
  apply le_antisymm
  · intro x hx
    have hfix : GradedAlgebra.proj G n x = x := by
      rw [GradedAlgebra.proj_apply]
      exact decompose_of_mem_same G hx
    have hmem := hproj (show x ∈ (⊤ : Submodule F A) from trivial)
    change GradedAlgebra.proj G n x ∈ T at hmem
    simpa only [hfix] using hmem
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change e i.1 ∈ G n
    simpa only [i.property] using he i.1

def pieceBasis (n : ℕ) : Basis {i : ι // w i = n} F (G n) :=
  (Basis.span (e.linearIndependent.comp (fun i : {i : ι // w i = n} ↦ i.1)
    Subtype.val_injective)).map (LinearEquiv.ofEq _ _ (piece_eq_span G e w he n).symm)

theorem pieceBasis_apply (n : ℕ) (i : {i : ι // w i = n}) :
    (pieceBasis G e w he n i : A) = e i := by
  rw [pieceBasis, Basis.map_apply]
  change (Basis.span (e.linearIndependent.comp (fun i : {i : ι // w i = n} ↦ i.1)
    Subtype.val_injective) i : A) = e i
  exact Basis.coe_span_apply _ i

end PaperP1.HomogeneousPieceBasis
