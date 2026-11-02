module

public import PaperP1.Asymptotics.KnownAlignmentRank
public import PaperP1.Arithmetic.NonalignedRankFieldBCN
public import PaperP1.Analysis.CriticalRankMass

/-! # Compatible pair ranks in every actual window, under the explicit BCN input -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairRankUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FreeComponentRank
  PaperP1.ShortBasisCurveScale PaperP1.CriticalRankMass

theorem compatible_pair_bound_succ (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
      x ≠ y → 0 < infiniteJointMoment L {x, y} →
        (pairIntersectionRank x y L : ℝ) ≤ (1 / 2 + ε) * ((L + 1 : ℕ) : ℝ) := by
  classical
  obtain ⟨Nnon, hnon⟩ := NonalignedRankFieldBCN.critical_rank_bound c κ hc hBCN ε hε C
  obtain ⟨Nalign, halign⟩ := KnownAlignmentRank.compatible_half_bound C ε hε
  refine ⟨max Nnon Nalign, ?_⟩
  intro N hN L x y hband hx hy hxy hq
  by_cases ha : CompressedTargetAlignment.Aligned 1 x y L
  · obtain ⟨a, b, hapos, hbpos, hcop, haB, hbB, hgeom⟩ := ha
    have hg : EnlargedPairGeometry.Geometric a b x y L := by
      simpa only [EnlargedPairGeometry.Geometric, one_mul, abs_sub_comm] using hgeom
    have h := (halign N (by omega) L a b x y hband hapos hbpos hcop (max_le haB hbB)
      hx hy hg hxy hq).2
    linarith only [h]
  · have h := hnon N (by omega) L hband x hx y hy ha
    have hcoef : (2 / 3) * Real.log 2 + ε ≤ 1 / 2 + ε := by linarith [rank_threshold_lt_half]
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _))

theorem compatible_pair_bound (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
      x ≠ y → 0 < infiniteJointMoment L {x, y} →
        (pairIntersectionRank x y L : ℝ) ≤ (1 / 2 + ε) * (L : ℝ) := by
  obtain ⟨Npair, hpair⟩ := compatible_pair_bound_succ c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨L₀, hL₀⟩ := succ_coefficient_eventually (1 / 2 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C (L₀ + 1)
  refine ⟨max Npair Ngeom, ?_⟩
  intro N hN L x y hband hx hy hxy hq
  obtain ⟨_hNtwo, hLlarge, _⟩ := hgeom N (by omega) L hband
  have hconv := hL₀ L (by omega)
  have h := hpair N (by omega) L x y hband hx hy hxy hq
  nlinarith only [h, hconv]

theorem nonaligned_pair_bound (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
      ¬ CompressedTargetAlignment.Aligned 1 x y L →
        (pairIntersectionRank x y L : ℝ) ≤ ((2 / 3) * Real.log 2 + ε) * (L : ℝ) := by
  obtain ⟨Npair, hpair⟩ := NonalignedRankFieldBCN.critical_rank_bound c κ hc hBCN
    (ε / 2) (by positivity) C
  obtain ⟨L₀, hL₀⟩ := succ_coefficient_eventually ((2 / 3) * Real.log 2 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C (L₀ + 1)
  refine ⟨max Npair Ngeom, ?_⟩
  intro N hN L x y hband hx hy hnon
  obtain ⟨_hNtwo, hLlarge, _⟩ := hgeom N (by omega) L hband
  have hconv := hL₀ L (by omega)
  have h := hpair N (by omega) L hband x hx y hy hnon
  nlinarith only [h, hconv]

end PaperP1.AllPairRankUnderBCN
