module

public import PaperP1.Model.RationalTriplePrivateRank
public import PaperP1.Asymptotics.BinaryRankPowers

/-! # Uniform actual probabilities at every primitive rational slope, including the strict gap -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalTriplePrivateProbability

open PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrivateNormalizedFamilies
  PaperP1.RationalTripleNormalizers PaperP1.RationalTripleUnionRank

theorem uniform_point_bound {N L u v w t : ℕ} {C : ℝ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C)
    (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u) (hprim : Nat.gcd (Nat.gcd u v) w = 1)
    (ht : 1 ≤ t) (hprivate : FiniteEvenSquareClasses.Private (valueUnion (scale u v w) (centres u v w t) L)) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet (centres u v w t)) ≤
      BinaryRankPowers.constant C (71 / 30) 5 * (N : ℝ) ^ (-71 / 30 : ℝ) := by
  rw [RationalTriplePrivateRank.actual_probability huv hvw hw2u ht hL hprivate]
  simpa only [neg_div] using
    BinaryRankPowers.upper hN (by norm_num) hband (extremal_union_rank huv hvw hw2u hprim ht hL)

theorem nonextremal_point_bound {N L u v w t : ℕ} {C : ℝ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C)
    (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u) (hprim : Nat.gcd (Nat.gcd u v) w = 1)
    (hne : ¬(u = 10 ∧ v = 12 ∧ w = 15))
    (ht : 1 ≤ t) (hprivate : FiniteEvenSquareClasses.Private (valueUnion (scale u v w) (centres u v w t) L)) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet (centres u v w t)) ≤
      BinaryRankPowers.constant C (43 / 18) 5 * (N : ℝ) ^ (-43 / 18 : ℝ) := by
  rw [RationalTriplePrivateRank.actual_probability huv hvw hw2u ht hL hprivate]
  simpa only [neg_div] using
    BinaryRankPowers.upper hN (by norm_num) hband (nonextremal_union_rank huv hvw hw2u hprim hne ht hL)

end PaperP1.RationalTriplePrivateProbability
