module

public import PaperP1.Model.CompatibleTripleJointBound
public import PaperP1.Model.PositiveMarginalRestriction
public import PaperP1.Asymptotics.CoarseConnectedTripleJointMass
public import PaperP1.Asymptotics.PairActivityUnderBCN
public import PaperP1.Asymptotics.IndependentTargetMass
public import PaperP1.Asymptotics.IncompatibleTripleReduction

/-! # Coarse decay of the full actual absolute triple activity under explicit BCN

The gap is `1/2 - (2/3) log 2 > 0`. This is a first vanishing bound,
not the sharper triple estimate claimed in the source manuscripts.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseTripleActivityUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NonalignedJointProbabilityUnderBCN PaperP1.PositiveMarginalRestriction

theorem uniform_positive_activity (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CompatibleActivitySplit.positive L (G.powersetCard 3) ≤ (N : ℝ) ^ (-tripleGap + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NM, hNM, hmass⟩ := CoarseConnectedTripleJointMass.uniform_connected_mass c κ hc hBCN C η hη
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption 8 (-tripleGap + η) η hη
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max NM (max NF NG), by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  calc
    _ ≤ 8 * TripleJointPopulations.connectedJointMass G L :=
      CompatibleTripleJointBound.positive_triple_activity_bound G L hL
    _ ≤ 8 * (N : ℝ) ^ (-tripleGap + η) :=
      mul_le_mul_of_nonneg_left (hmass N (by omega) L hband G hG) (by norm_num)
    _ ≤ (N : ℝ) ^ ((-tripleGap + η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_absolute_activity (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CompatibleActivitySplit.absolute L (G.powersetCard 3) ≤ (N : ℝ) ^ (-tripleGap + ε) := by
  let η := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NP, hNP, hpositive⟩ := uniform_positive_activity c κ hc hBCN C η hη
  obtain ⟨NI, hincompatible⟩ := IncompatibleTripleReduction.reduced_bound C η hη
  obtain ⟨ND, hdeficit⟩ := IndependentTargetMass.deficit_bound C η hη
  obtain ⟨NA, hNA, hpair⟩ := PairActivityUnderBCN.uniform_pair_activity c κ hc hBCN C η hη
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption 3 (-tripleGap + 2 * η) (ε / 2) (by positivity)
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max NP (max NI (max ND (max NA (max NF NG)))), by omega, ?_⟩
  intro N hN L hband G hG
  let P := positiveGround G L
  have hP : P ⊆ dyadicBlock N := (positiveGround_subset G L).trans hG
  have hp : ∀ x ∈ P, 0 < infiniteMarginal x L := fun _ hx ↦ marginal_positive hx
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hd : IndependentTargetDeficit.deficit P L ≤ (N : ℝ) ^ (-1 + 2 * η) := by
    calc
      _ ≤ CompatibleActivitySplit.absolute L (P.powersetCard 2) * (N : ℝ) ^ (-1 / 2 + η) :=
        hdeficit N (by omega) L P hband hP
      _ ≤ (N : ℝ) ^ (-1 / 2 + η) * (N : ℝ) ^ (-1 / 2 + η) :=
        mul_le_mul_of_nonneg_right (hpair N (by omega) L hband P hP) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  have hi : CompatibleActivitySplit.incompatibleAbsolute L (P.powersetCard 3) ≤
      2 * (N : ℝ) ^ (-tripleGap + 2 * η) := by
    have hgap := tripleGap_lt_half
    have hfirst : (N : ℝ) ^ (-3 / 2 + η) ≤ (N : ℝ) ^ (-tripleGap + 2 * η) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hgap, hη])
    have hsecond : (N : ℝ) ^ (-1 + 2 * η) ≤ (N : ℝ) ^ (-tripleGap + 2 * η) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hgap])
    have h := hincompatible N (by omega) L P hband hP hp
    linarith only [h, hd, hfirst, hsecond]
  have hpbound : CompatibleActivitySplit.positive L (P.powersetCard 3) ≤
      (N : ℝ) ^ (-tripleGap + 2 * η) :=
    (hpositive N (by omega) L hband P hP).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hη]))
  have hrestrict : CompatibleActivitySplit.absolute L (G.powersetCard 3) =
      CompatibleActivitySplit.absolute L (P.powersetCard 3) :=
    sum_restrict G L 3 abs abs_zero
  calc
    _ = CompatibleActivitySplit.absolute L (P.powersetCard 3) := hrestrict
    _ = CompatibleActivitySplit.positive L (P.powersetCard 3) +
        CompatibleActivitySplit.incompatibleAbsolute L (P.powersetCard 3) :=
      CompatibleActivitySplit.absolute_split L hL _
    _ ≤ 3 * (N : ℝ) ^ (-tripleGap + 2 * η) := by linarith only [hpbound, hi]
    _ ≤ (N : ℝ) ^ ((-tripleGap + 2 * η) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_vanishing_activity (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CompatibleActivitySplit.absolute L (G.powersetCard 3) ≤ (N : ℝ) ^ (-tripleGap / 2) := by
  have hgap := tripleGap_pos
  simpa only [show -tripleGap + tripleGap / 2 = -tripleGap / 2 by ring] using
    uniform_absolute_activity c κ hc hBCN C (tripleGap / 2) (by positivity)

end PaperP1.CoarseTripleActivityUnderBCN
