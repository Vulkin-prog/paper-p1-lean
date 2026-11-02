module

public import PaperP1.Arithmetic.RepeatedCoefficientUnionRank
public import PaperP1.Asymptotics.ThreeWindowRankProbability
public import PaperP1.Asymptotics.EnlargedSourceTargetResidual
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Physical repeated-slope targets above enlarged sources have actual probability at most N^(-5/2+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedPhysicalTargetTripleProbability

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ScaledTargetValues PaperP1.PrivateNormalizedFamilies

theorem uniform_point_bound {a b : ℕ} (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L c d x y z t : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < c → 0 < d → c.Coprime d → d ≤ (L + 1) ^ J →
      x ∈ dyadicBlock N → y ∈ dyadicBlock N → z ∈ dyadicBlock N → x ≠ z → y ≠ z →
      (c = a * d ∨ c = b * d) →
      EnlargedPairGeometry.Geometric a b x y L →
      ∀ i : Fin (L + 1), startCompleteVertexLabel x L i = a * t →
        ∀ h : ℤ, |h| ≤ ((L + 1) ^ J : ℕ) → (d : ℤ) * z = (c : ℤ) * t + h →
          infiniteJointMoment L {x, y, z} ≤ (N : ℝ) ^ (-5 / 2 + ε) := by
  let η := min (ε / 4) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε / 4 := min_le_left _ _
  have hηq : η ≤ 1 / 4 := min_le_right _ _
  have hαη : 0 ≤ (5 / 2 : ℝ) - η := by linarith only [hηq]
  have hεη : 0 < ε - η := by linarith only [hηε, hε]
  obtain ⟨NR, hr⟩ := EnlargedSourceTargetResidual.row_rank_sublinear C η hη ha hab.le J
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := HalfCountSchedule.factor_absorption
    (BinaryRankPowers.constant C ((5 / 2 : ℝ) - η) (1 + 2 + η)) (-5 / 2 + η) (ε - η) hεη
  refine ⟨max 10 (max NR (max NG NP)), by omega, ?_⟩
  intro N hN L c d x y z t hband hc hd hcd hdH hx hy hz hxz hyz hphys hsourceGeom i hbaseX h hh htarget
  by_cases hprob : 0 < infiniteJointMoment L {x, y, z}
  · have hb : 0 < b := ha.trans hab
    have ha2 : 2 ≤ a := by omega
    have hb2 : 2 ≤ b := by omega
    have hx2 : 2 ≤ x := by have hh := (mem_Ico.mp hx).1; omega
    have hy2 : 2 ≤ y := by have hh := (mem_Ico.mp hy).1; omega
    have hz2 : 2 ≤ z := by have hh := (mem_Ico.mp hz).1; omega
    have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
    let X : Fin 3 → ℕ := ![x, y, z]
    let q : Fin 3 → ℕ := ![b * c, a * c, a * b * d]
    have hq : ∀ k, 0 < q k := by
      intro k
      fin_cases k
      · exact Nat.mul_pos hb hc
      · exact Nat.mul_pos ha hc
      · exact Nat.mul_pos (Nat.mul_pos ha hb) hd
    have hX : ∀ k, 2 ≤ X k := by intro k; fin_cases k <;> assumption
    have hS : valueUnion q X L = allValues a b c d x y z L :=
      AlignedTargetCanonicalRank.allValues_eq_family a b c d x y z L
    have hrow := hr N (by omega) L c d x y z t hband hc hd hdH hx hy hz hsourceGeom i hbaseX h hh htarget
    have hfull := Submodule.finrank_mono (FiniteResidualRank.kernel_le_rows (allValues a b c d x y z L)
      (TwoProgressionPrimeRows.exceptionalPrimes (6 * b * (L + 1)) c (a * b * d)))
    have hdef : (Module.finrank F₂ (FiniteResidualRank.valueKernel (valueUnion q X L)) : ℝ) ≤ η * (L + 1) := by
      rw [hS]
      have hfullR : (Module.finrank F₂ (FiniteResidualRank.valueKernel (allValues a b c d x y z L)) : ℝ) ≤
          Module.finrank F₂ (CoverGraphResolution.rowSolutions (PrimeRowComponents.rows
            (allValues a b c d x y z L) (TwoProgressionPrimeRows.exceptionalPrimes (6 * b * (L + 1)) c (a * b * d)))) := by
        exact_mod_cast hfull
      exact hfullR.trans (by simpa only [Nat.cast_add, Nat.cast_one] using hrow)
    have hcan : (5 / 2 : ℝ) * L - 1 ≤ (((valueUnion q X L).card - 1 : ℕ) : ℝ) := by
      rw [hS]
      obtain ⟨rfl, hca | hcb⟩ := RepeatedCoefficientUnionRank.reduced_physical hcd hphys
      · subst c
        exact RepeatedCoefficientUnionRank.physical_a_rank ha hb2 hcop hx2 hy2 hz2
          (CompatibleWindowOverlap.compatible_pair_overlap_le_one (by omega) (by omega) hxz hL
            (CompatibleWindowOverlap.triple_joint_pairs hprob).1)
      · subst c
        exact RepeatedCoefficientUnionRank.physical_b_rank ha2 hb hcop hx2 hy2 hz2
          (CompatibleWindowOverlap.compatible_pair_overlap_le_one (by omega) (by omega) hyz hL
            (CompatibleWindowOverlap.triple_joint_pairs hprob).2)
    have hbinary := ThreeWindowRankProbability.upper (by omega : 2 ≤ N) hL hband hαη q X hq hX hcan hdef
    rw [show -((5 / 2 : ℝ) - η) = -5 / 2 + η by ring] at hbinary
    have habsorb : BinaryRankPowers.constant C ((5 / 2 : ℝ) - η) (1 + 2 + η) * (N : ℝ) ^ (-5 / 2 + η) ≤
        (N : ℝ) ^ (-5 / 2 + ε) := by
      simpa only [show (-5 / 2 + η) + (ε - η) = (-5 / 2 : ℝ) + ε by ring] using hp N (by omega)
    have hsupport : FiniteFamilyEnumeration.tupleSet X = {x, y, z} := by
      have hu : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      rw [FiniteFamilyEnumeration.tupleSet, hu]
      simp only [image_insert, image_singleton]
      rfl
    rw [hsupport] at hbinary
    exact hbinary.trans habsorb
  · exact (le_of_not_gt hprob).trans (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end PaperP1.EnlargedPhysicalTargetTripleProbability
