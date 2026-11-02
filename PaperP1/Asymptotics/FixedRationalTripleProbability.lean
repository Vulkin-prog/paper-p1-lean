module

public import PaperP1.Asymptotics.FixedRationalTripleResidual
public import PaperP1.Asymptotics.RationalTripleEvenProbability
public import PaperP1.Asymptotics.RationalTriplePrivateMass
public import PaperP1.Asymptotics.HalfCountSchedule
public import PaperP1.Model.NormalizedFamilyDefectRank

/-! # All actual rational triples at bounded fixed slope height satisfy the sharp upper exponents -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedRationalTripleProbability

open PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrivateNormalizedFamilies
  PaperP1.RationalTripleNormalizers

theorem uniform_point_bound (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (hε : 0 < ε) (nonextremal : Bool) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L u v w t : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      u < v → v < w → w < 2 * u → Nat.gcd (Nat.gcd u v) w = 1 → w ≤ Q → 1 ≤ t →
      u * t ∈ dyadicBlock N → (nonextremal = true → ¬(u = 10 ∧ v = 12 ∧ w = 15)) →
      infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet (centres u v w t)) ≤
        (N : ℝ) ^ (-RationalTriplePrivateMass.alpha nonextremal + ε) := by
  let α := RationalTriplePrivateMass.alpha nonextremal
  let η := min (ε / 4) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε / 4 := min_le_left _ _
  have hηq : η ≤ 1 / 4 := min_le_right _ _
  have hα : 2 ≤ α := by cases nonextremal <;> norm_num [α, RationalTriplePrivateMass.alpha]
  have hαη : 0 ≤ α - η := by linarith only [hα, hηq]
  have hεη : 0 < ε - η := by linarith only [hηε, hε]
  obtain ⟨NR, _hNR, hr⟩ := FixedRationalTripleResidual.full_kernel_sublinear Q hQ C η hη
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := HalfCountSchedule.factor_absorption
    (BinaryRankPowers.constant C (α - η) (5 + η)) (-α + η) (ε - η) hεη
  refine ⟨max 10 (max NR (max NG NP)), by omega, ?_⟩
  intro N hN L u v w t hband huv hvw hw2u hprim hwQ ht hx hnon
  have hu : 2 ≤ u := by omega
  have hL : 1 ≤ L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  let S := valueUnion (scale u v w) (centres u v w t) L
  let R := Module.finrank F₂ (⨆ i, squareClassSpace (centres u v w t i) L : Submodule F₂ (ℕ →₀ F₂))
  have hdef := hr N (by omega) L u v w t hband hu huv.le hvw.le hwQ ht hx
  have hcard := NormalizedFamilyDefectRank.common_rank_defect (by omega : 0 < 3)
    (scale u v w) (centres u v w t) (scale_pos (by omega) (by omega) (by omega))
    (centres_ge_two hu huv.le hvw.le ht) (origin u v w t) (common_mem hu huv.le hvw.le ht hL)
  change S.card - 1 ≤ R + Module.finrank F₂ (FiniteResidualRank.valueKernel S) at hcard
  have hcardR : ((S.card - 1 : ℕ) : ℝ) ≤ (R : ℝ) + Module.finrank F₂ (FiniteResidualRank.valueKernel S) := by
    exact_mod_cast hcard
  have hgeom : α * L - 5 ≤ ((S.card - 1 : ℕ) : ℝ) := by
    cases nonextremal
    · exact RationalTripleUnionRank.extremal_union_rank huv hvw hw2u hprim ht hL
    · exact RationalTripleUnionRank.nonextremal_union_rank huv hvw hw2u hprim (hnon rfl) ht hL
  have hR : (α - η) * L - (5 + η) ≤ (R : ℝ) := by
    change (Module.finrank F₂ (FiniteResidualRank.valueKernel S) : ℝ) ≤ η * (L + 1) at hdef
    nlinarith only [hdef, hcardR, hgeom]
  have hbinary := BinaryRankPowers.upper (by omega : 2 ≤ N) hαη hband hR
  rw [show -(α - η) = -α + η by ring] at hbinary
  have habsorb : BinaryRankPowers.constant C (α - η) (5 + η) * (N : ℝ) ^ (-α + η) ≤
      (N : ℝ) ^ (-α + ε) := by
    simpa only [show (-α + η) + (ε - η) = -α + ε by ring] using hp N (by omega)
  exact (NormalizedFamilyDefectRank.actual_joint_le_rank (centres u v w t) (by omega)).trans
    (hbinary.trans habsorb)

end PaperP1.FixedRationalTripleProbability
