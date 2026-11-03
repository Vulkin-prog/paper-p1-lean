module

public import PaperP1.Asymptotics.StrongNonalignedTripleProfileUnderBCN
public import PaperP1.Asymptotics.TripleRankUnderBCN

/-! # Every connected triple above a strong locally nonaligned pair

The rank restriction of Proposition 12.2 is discharged using the proved
compatible triple bound. Zero actual joint probabilities are retained.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StrongNoExactTripleMassUnderBCN

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ ConnectedWindowFamilies.Connected L I ∧
        ∃ x ∈ I, ∃ y ∈ I, x ≠ y ∧ ActualOffsetNonalignment.NoExact x y L ∧
          θ * L ≤ (FreeComponentRank.pairIntersectionRank x y L : ℝ)) →
      (∑ I ∈ F, infiniteJointMoment L I) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨NR, hr⟩ := TripleRankUnderBCN.uniform_triple_nullity c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := StrongNonalignedTripleProfileUnderBCN.main_12_2 c κ hc hBCN
    C θ (3 / 2 + ε / 2) (ε / 2) hθ (by positivity) (by positivity)
  refine ⟨3 + NR + NM, by omega, ?_⟩
  intro N hN L hband F hF
  classical
  let P := fun I ↦ 0 < infiniteJointMoment L I
  let FP := F.filter P
  have hpositive : ∑ I ∈ F, infiniteJointMoment L I = ∑ I ∈ FP, infiniteJointMoment L I := by
    rw [show FP = F.filter P from rfl, sum_filter]
    apply sum_congr rfl
    intro I _hI
    by_cases hq : 0 < infiniteJointMoment L I
    · exact (ite_eq_left hq).symm
    · have hz : infiniteJointMoment L I = 0 := le_antisymm (le_of_not_gt hq)
        (infiniteJointMoment_nonneg L I)
      rw [ite_eq_right hq]
      exact hz
  have hh := hm N (by omega) L hband FP (by
    intro I hI
    obtain ⟨hIF, hq⟩ := mem_filter.mp hI
    obtain ⟨hdyadic, hcard, hconn, hstrong⟩ := hF I hIF
    exact ⟨hdyadic, hcard, hconn, hr N (by omega) L hband I hdyadic hcard hq, hstrong⟩)
  have hmin : min (3 / 2 : ℝ) (3 - (3 / 2 + ε / 2)) = 3 - (3 / 2 + ε / 2) :=
    min_eq_right (by linarith only [hε])
  rw [hmin] at hh
  rw [hpositive]
  convert hh using 1
  congr 1
  ring

end PaperP1.StrongNoExactTripleMassUnderBCN
