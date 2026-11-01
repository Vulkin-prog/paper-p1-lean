module

public import PaperP1.Algebra.FiniteSetValueSpan
public import PaperP1.Algebra.QuotientRank

/-! # Relative zero-sum rank loss is bounded by matches plus the true union kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteSetRelativeRank

open Finset PaperP1.FiniteSetValueSpan

variable {K V E : Type*} [DivisionRing K] [DecidableEq V] [AddCommGroup E] [Module K E]

def relativeKernel (f : V → E) (S T : Finset V) :
    Submodule K (LinearMap.ker (EvenSupportRank.sumMap K T)) :=
  (span (K := K) f S).comap (EvenImage.evenMap (K := K) (data f T))

omit [DecidableEq V] in
theorem relative_rank_le_even_dimension (f : V → E) (S T : Finset V) :
    Module.finrank K (relativeKernel (K := K) f S T) ≤ T.card - 1 := by
  have h := Submodule.finrank_le (relativeKernel (K := K) f S T)
  rw [EvenSupportRank.kernel_sum_finrank, Fintype.card_coe] at h
  exact h

theorem matches_add_residual (f : V → E) (S T : Finset V) :
    Module.finrank K (relativeKernel (K := K) f S T) ≤
      (S ∩ T).card + Module.finrank K (valueKernel (K := K) f (S ∪ T)) := by
  by_cases hT : T.Nonempty
  · have hjoin := QuotientRank.joined_rank_add_kernel (span (K := K) f S)
      (EvenImage.evenMap (K := K) (data f T))
    rw [EvenSupportRank.kernel_sum_finrank, Fintype.card_coe] at hjoin
    change Module.finrank K ↥(span (K := K) f S ⊔ evenSpace (K := K) f T) +
      Module.finrank K (relativeKernel (K := K) f S T) =
      Module.finrank K (span (K := K) f S) + (T.card - 1) at hjoin
    have hfull := rank_add_kernel (K := K) f (S ∪ T)
    have hupper := full_union_rank_le_old_even_add_one (K := K) f S T
    have hold := rank_le_card (K := K) f S
    have hcard := card_union_add_card_inter S T
    have hTpos := hT.card_pos
    omega
  · have hbound := relative_rank_le_even_dimension (K := K) f S T
    have hTcard : T.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hT)
    omega

theorem matches_add_residual_of_old_le (f : V → E) (S T : Finset V)
    (W : Submodule K E) (hW : W ≤ span (K := K) f S) :
    Module.finrank K (W.comap (EvenImage.evenMap (K := K) (data f T))) ≤
      (S ∩ T).card + Module.finrank K (valueKernel (K := K) f (S ∪ T)) := by
  have hle : W.comap (EvenImage.evenMap (K := K) (data f T)) ≤ relativeKernel (K := K) f S T :=
    fun _ hw ↦ hW hw
  exact (Submodule.finrank_mono hle).trans (matches_add_residual (K := K) f S T)

end PaperP1.FiniteSetRelativeRank
