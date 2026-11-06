module

public import PaperP1.Arithmetic.ExactDegreeSourceSurfaceCover
public import PaperP1.Arithmetic.SourceSurfaceCoverUnderP3

/-! # One exact source covering constant works for all allowed finite source sizes before all coefficients and heights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformExactSourceCoverFromP3

open Finset ExactDegreeSourceSurfaceCover

theorem of_hypersurface_covers (kmax D : ℕ)
    (hP3 : ∀ k : ℕ, k ≤ kmax → UniformP3HypersurfaceCover.UniformCover (2 ^ k * D ^ 2)) :
    UniformCover kmax D := by
  classical
  intro δ hδ
  by_cases hD : 0 < D
  · have hsize (i : Fin (kmax + 1)) : ∃ (B : ℕ) (C : ℝ), 0 < C ∧ CoverAtSize i.val D hD B C δ := by
      obtain ⟨M, A, hA, hcover⟩ := hP3 i.val (by have := i.isLt; omega) δ hδ
      exact SourceSurfaceCoverUnderP3.of_cover_at_degree i.val D hD δ hδ M A hA hcover
    choose B C hC hsize using hsize
    have hsum : 0 < ∑ i, C i := Finset.sum_pos (fun i _hi ↦ hC i) Finset.univ_nonempty
    refine ⟨Finset.univ.sup B, ∑ i, C i, hsum, ?_⟩
    intro hD' k hk
    let i : Fin (kmax + 1) := ⟨k, by omega⟩
    apply CoverAtSize.mono (hsize i)
    · exact Finset.le_sup (f := B) (Finset.mem_univ i)
    · exact Finset.single_le_sum (fun j _hj ↦ (hC j).le) (Finset.mem_univ i)
  · refine ⟨0, 1, by norm_num, ?_⟩
    intro hD'
    exact False.elim (hD hD')

end PaperP1.UniformExactSourceCoverFromP3
