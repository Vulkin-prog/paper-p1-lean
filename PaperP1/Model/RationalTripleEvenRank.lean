module

public import PaperP1.Arithmetic.RationalTripleUnionRank
public import PaperP1.Model.NormalizedFamilyDilation

/-! # Exact rational-triple probabilities under full even rank, without raw private primes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalTripleEvenRank

open PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrivateNormalizedFamilies
  PaperP1.RationalTripleNormalizers

theorem actual_probability {u v w t L : ℕ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (ht : 1 ≤ t) (hL : 1 ≤ L)
    (hfull : EvenIndependentValues.Independent (valueUnion (scale u v w) (centres u v w t) L)) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet (centres u v w t)) =
      (2 ^ ((valueUnion (scale u v w) (centres u v w t) L).card - 1) : ℝ)⁻¹ := by
  have hu : 2 ≤ u := by omega
  exact EvenNormalizedFamilies.common_probability (by omega : 0 < 3) (scale u v w) (centres u v w t)
    (scale_pos (by omega) (by omega) (by omega)) (centres_ge_two hu huv.le hvw.le ht) (by omega)
    (origin u v w t) (common_mem hu huv.le hvw.le ht hL) hfull
    (exclusive (by omega) (by omega) (by omega) ht L)

theorem effective_rank {u v w t L : ℕ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (ht : 1 ≤ t) (hL : 1 ≤ L)
    (hfull : EvenIndependentValues.Independent (valueUnion (scale u v w) (centres u v w t) L)) :
    Module.finrank F₂ (⨆ i, squareClassSpace (centres u v w t i) L : Submodule F₂ (ℕ →₀ F₂)) =
      (valueUnion (scale u v w) (centres u v w t) L).card - 1 := by
  have hu : 2 ≤ u := by omega
  exact EvenNormalizedFamilies.common_joint_rank (by omega : 0 < 3) (scale u v w) (centres u v w t)
    (scale_pos (by omega) (by omega) (by omega)) (centres_ge_two hu huv.le hvw.le ht)
    (origin u v w t) (common_mem hu huv.le hvw.le ht hL) hfull

end PaperP1.RationalTripleEvenRank
