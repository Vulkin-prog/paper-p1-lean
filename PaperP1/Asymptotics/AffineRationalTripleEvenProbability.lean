module

public import PaperP1.Arithmetic.AffineRationalTripleUnionRank
public import PaperP1.Model.NormalizedFamilyDefectRank
public import PaperP1.Asymptotics.BinaryRankPowers

/-! # Sharp actual probabilities with arbitrary rational-window translations and connected normalized overlap -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineRationalTripleEvenProbability

open PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.NormalizedWindowSets
  PaperP1.PrivateNormalizedFamilies PaperP1.RationalTripleNormalizers

theorem uniform_point_bound {N L u v w : ℕ} {C : ℝ} (hN : 2 ≤ N) (hL : 0 < L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C)
    (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u) (hprim : Nat.gcd (Nat.gcd u v) w = 1)
    (X : Fin 3 → ℕ) (hX : ∀ i, 2 ≤ X i)
    (hfull : EvenIndependentValues.Independent (valueUnion (scale u v w) X L))
    (hconn : (ConnectedValueUnions.intersectionGraph (fun i ↦ normalized (scale u v w i) (X i) L)).Connected) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) ≤
      BinaryRankPowers.constant C (71 / 30) 3 * (N : ℝ) ^ (-71 / 30 : ℝ) := by
  have hc := scale_pos (by omega : 0 < u) (by omega : 0 < v) (by omega : 0 < w)
  have hq := NormalizedFamilyDefectRank.actual_joint_le_rank X hL
  rw [EvenNormalizedFamilies.connected_joint_rank (scale u v w) X hc hX hfull hconn] at hq
  apply hq.trans
  simpa only [neg_div] using BinaryRankPowers.upper hN (by norm_num) hband
    (AffineRationalTripleUnionRank.extremal_union_rank (L := L) huv hvw hw2u hprim X hX)

theorem nonextremal_point_bound {N L u v w : ℕ} {C : ℝ} (hN : 2 ≤ N) (hL : 0 < L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C)
    (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u) (hprim : Nat.gcd (Nat.gcd u v) w = 1)
    (hne : ¬(u = 10 ∧ v = 12 ∧ w = 15)) (X : Fin 3 → ℕ) (hX : ∀ i, 2 ≤ X i)
    (hfull : EvenIndependentValues.Independent (valueUnion (scale u v w) X L))
    (hconn : (ConnectedValueUnions.intersectionGraph (fun i ↦ normalized (scale u v w i) (X i) L)).Connected) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) ≤
      BinaryRankPowers.constant C (43 / 18) 3 * (N : ℝ) ^ (-43 / 18 : ℝ) := by
  have hc := scale_pos (by omega : 0 < u) (by omega : 0 < v) (by omega : 0 < w)
  have hq := NormalizedFamilyDefectRank.actual_joint_le_rank X hL
  rw [EvenNormalizedFamilies.connected_joint_rank (scale u v w) X hc hX hfull hconn] at hq
  apply hq.trans
  simpa only [neg_div] using BinaryRankPowers.upper hN (by norm_num) hband
    (AffineRationalTripleUnionRank.nonextremal_union_rank (L := L) huv hvw hw2u hprim hne X hX)

end PaperP1.AffineRationalTripleEvenProbability
