module

public import PaperP1.Model.CompressedJointMoments

/-! # A compatible actual source pair has absolute centered coefficient at most its actual joint probability -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CenteredSourcePairBound

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem pointwise (L : ℕ) (hL : 0 < L) (e : Finset ℕ) (he : e.card = 2)
    (hq : 0 < infiniteJointMoment L e) :
    0 ≤ infiniteCenteredCoefficient L e ∧ |infiniteCenteredCoefficient L e| ≤ infiniteJointMoment L e := by
  have hqeq := infiniteJointMoment_exact_of_pos (e.sup fun x ↦ x + L) L e hL
    (fun x hx ↦ le_sup (f := fun x ↦ x + L) hx) hq
  have hp : 0 ≤ ∏ x ∈ e, infiniteMarginal x L :=
    prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hpow : (1 : ℝ) ≤ 2 ^ runRelativeNullity L e := one_le_pow₀ (by norm_num)
  have hprod := mul_le_mul_of_nonneg_left hpow hp
  change infiniteJointMoment L e = (∏ x ∈ e, infiniteMarginal x L) * (2 ^ runRelativeNullity L e : ℝ) at hqeq
  have hcent := CompressedJointMoments.centered_pair L e he
  have hnonneg : 0 ≤ infiniteCenteredCoefficient L e := by nlinarith only [hqeq, hprod, hcent]
  refine ⟨hnonneg, ?_⟩
  rw [abs_of_nonneg hnonneg]
  linarith only [hp, hcent]

end PaperP1.CenteredSourcePairBound
