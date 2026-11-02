module

public import PaperP1.Model.ExactContactEdges
public import PaperP1.Model.PairActivityHostCap
public import PaperP1.Model.PairRowActivity

/-! # Exact-contact covariance vanishes on every regular full union window -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExactContactCentered

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ExactContactEdges

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem zero_on_regular_union {N L x : ℕ} (hx : 0 < x) (hL : 0 < L)
    (hreg : x ∈ RegularStarts.regularStarts N (2 * L)) :
    infiniteCenteredCoefficient L {x, x + L} = 0 := by
  apply PairActivityHostCap.centered_zero_of_zero_loss hx (by omega) (by omega) hL
  unfold NormalizedPairRankLoss.pairLoss
  rw [ContactWindowSpan.joined_space hx, (RegularStarts.mem_regularStarts.mp hreg).2, Nat.sub_self]

theorem absolute_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hp : ∀ x ∈ dyadicBlock N, infiniteMarginal x L ≤ P)
    (hq : ∀ x ∈ starts N L, infiniteJointMoment L {x, x + L} ≤ Q) :
    CompatibleActivitySplit.absolute L (edges N L) ≤
      ((RegularStarts.irregularStarts N (2 * L)).card : ℝ) * (Q + P ^ 2) := by
  let A := (starts N L).filter fun x ↦ x ∈ RegularStarts.irregularStarts N (2 * L)
  have heq : CompatibleActivitySplit.absolute L (edges N L) =
      ∑ x ∈ A, |infiniteCenteredCoefficient L {x, x + L}| := by
    rw [CompatibleActivitySplit.absolute, edges, sum_image (map_injective L).injOn]
    symm
    apply sum_subset (filter_subset _ _)
    intro x hx hnot
    have hxN := (mem_filter.mp hx).1
    have hreg : x ∈ RegularStarts.regularStarts N (2 * L) := by
      by_contra hr
      exact hnot (mem_filter.mpr ⟨hx, mem_sdiff.mpr ⟨hxN, hr⟩⟩)
    rw [zero_on_regular_union (by have h := (mem_Ico.mp hxN).1; omega) hL hreg, abs_zero]
  rw [heq]
  calc
    _ ≤ ∑ _x ∈ A, (Q + P ^ 2) := by
      apply sum_le_sum
      intro x hx
      have hxS := (mem_filter.mp hx).1
      obtain ⟨hxN, hyN⟩ := mem_filter.mp hxS
      have hprod : infiniteMarginal x L * infiniteMarginal (x + L) L ≤ P ^ 2 := by
        simpa only [pow_two] using mul_le_mul (hp x hxN) (hp (x + L) hyN)
          (MissingBlockProbabilities.infiniteMarginal_nonneg (x + L) L) hP
      exact (PairRowActivity.pair_absolute_bound L x (x + L) (by omega)).trans (add_le_add (hq x hxS) hprod)
    _ = (A.card : ℝ) * (Q + P ^ 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
      exact_mod_cast card_le_card (show A ⊆ RegularStarts.irregularStarts N (2 * L) from fun _ h ↦ (mem_filter.mp h).2))
      (add_nonneg hQ (sq_nonneg P))

end PaperP1.ExactContactCentered
