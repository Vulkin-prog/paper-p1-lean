module

public import PaperP1.Model.ConnectedTargetDependence
public import PaperP1.Model.TripleJointReconstruction
public import PaperP1.Model.TripleJointPopulations
public import PaperP1.Model.IndependentTargetDeficit
public import PaperP1.Model.AbsoluteActivityDecomposition
public import PaperP1.Model.CompatibleActivitySplit
public import PaperP1.Model.FamilyIndependentMass
public import PaperP1.Combinatorics.TriplePairIncidence

/-! # Actual connected triple joint mass has coefficient one in its centered-activity reduction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedTriplePositiveReduction

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

theorem pair_cost (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    (∑ T ∈ connectedFamilies G L 3, ∑ z ∈ T,
      |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L) ≤
        IndependentTargetDeficit.deficit G L := by
  classical
  rw [IndependentTargetDeficit.incidence_formula]
  apply TriplePairIncidence.restricted_erased_sum_le G 2 (connectedFamilies G L 3)
    (filter_subset _ _) (fun e z ↦ |infiniteCenteredCoefficient L e| * infiniteMarginal z L)
    (fun e z ↦ mul_nonneg (abs_nonneg _) (MissingBlockProbabilities.infiniteMarginal_nonneg z L))
    (fun e z ↦ IndependentTargetDeficit.dependentPair L e ∧ IndependentTargetDeficit.targetDependent L e z)
  intro T hT z hz hn
  obtain ⟨hT, hconn⟩ := mem_filter.mp hT
  have hcard := (mem_powersetCard.mp hT).2
  have hc : infiniteCenteredCoefficient L (T.erase z) ≠ 0 := by
    intro hc
    exact hn (by rw [hc, abs_zero, zero_mul])
  refine ⟨?_, ConnectedTargetDependence.every_target L T (by omega) hconn hz⟩
  change 0 < runRelativeNullity L (T.erase z)
  apply Nat.pos_of_ne_zero
  intro hzero
  have he := card_erase_add_one hz
  exact hc (AbsoluteActivityDecomposition.centered_zero_direct L hL (T.erase z)
    (card_pos.mp (by omega)) hzero)

theorem finite_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    TripleJointPopulations.connectedJointMass G L ≤
      CompatibleActivitySplit.absolute L (connectedFamilies G L 3) +
      IndependentTargetDeficit.deficit G L +
      FamilyIndependentMass.independentMass (connectedFamilies G L 3) L := by
  classical
  calc
    _ ≤ ∑ T ∈ connectedFamilies G L 3, (|infiniteCenteredCoefficient L T| +
        (∑ z ∈ T, |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L) +
        ∏ z ∈ T, infiniteMarginal z L) := by
      apply sum_le_sum
      intro T hT
      exact TripleJointReconstruction.absolute_bound L T (mem_powersetCard.mp (mem_filter.mp hT).1).2
    _ = CompatibleActivitySplit.absolute L (connectedFamilies G L 3) +
        (∑ T ∈ connectedFamilies G L 3, ∑ z ∈ T,
          |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L) +
        FamilyIndependentMass.independentMass (connectedFamilies G L 3) L := by
      rw [sum_add_distrib, sum_add_distrib]
      rfl
    _ ≤ _ := add_le_add (add_le_add le_rfl (pair_cost G L hL)) le_rfl

theorem signed_error (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    |TripleJointPopulations.connectedJointMass G L -
      CompatibleActivitySplit.signed L (connectedFamilies G L 3)| ≤
      IndependentTargetDeficit.deficit G L +
      FamilyIndependentMass.independentMass (connectedFamilies G L 3) L := by
  classical
  rw [TripleJointPopulations.connectedJointMass, CompatibleActivitySplit.signed, ← sum_sub_distrib]
  calc
    _ ≤ ∑ T ∈ connectedFamilies G L 3, |infiniteJointMoment L T - infiniteCenteredCoefficient L T| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ connectedFamilies G L 3,
        ((∑ z ∈ T, |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L) +
          ∏ z ∈ T, infiniteMarginal z L) := by
      apply sum_le_sum
      intro T hT
      exact TripleJointReconstruction.error_bound L T (mem_powersetCard.mp (mem_filter.mp hT).1).2
    _ = (∑ T ∈ connectedFamilies G L 3, ∑ z ∈ T,
          |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L) +
        FamilyIndependentMass.independentMass (connectedFamilies G L 3) L := sum_add_distrib
    _ ≤ _ := add_le_add (pair_cost G L hL) le_rfl

theorem incompatible_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    CompatibleActivitySplit.incompatibleAbsolute L (connectedFamilies G L 3) ≤
      IndependentTargetDeficit.deficit G L +
      FamilyIndependentMass.independentMass (connectedFamilies G L 3) L := by
  classical
  let f := fun T : Finset ℕ ↦
    (∑ z ∈ T, |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L) +
      ∏ z ∈ T, infiniteMarginal z L
  calc
    _ ≤ ∑ T ∈ (connectedFamilies G L 3).filter (fun T ↦ infiniteJointMoment L T = 0), f T := by
      apply sum_le_sum
      intro T hT
      obtain ⟨hTc, hzero⟩ := mem_filter.mp hT
      have h := TripleJointReconstruction.error_bound L T (mem_powersetCard.mp (mem_filter.mp hTc).1).2
      simpa only [hzero, zero_sub, abs_neg] using h
    _ ≤ ∑ T ∈ connectedFamilies G L 3, f T := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro T _ _
      exact add_nonneg (sum_nonneg fun z _ ↦ mul_nonneg (abs_nonneg _)
        (MissingBlockProbabilities.infiniteMarginal_nonneg z L))
        (prod_nonneg fun z _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg z L)
    _ = (∑ T ∈ connectedFamilies G L 3, ∑ z ∈ T,
          |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L) +
        FamilyIndependentMass.independentMass (connectedFamilies G L 3) L := sum_add_distrib
    _ ≤ _ := add_le_add (pair_cost G L hL) le_rfl

theorem absolute_error (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    |TripleJointPopulations.connectedJointMass G L -
      CompatibleActivitySplit.absolute L (connectedFamilies G L 3)| ≤
      3 * (IndependentTargetDeficit.deficit G L +
        FamilyIndependentMass.independentMass (connectedFamilies G L 3) L) := by
  let F := connectedFamilies G L 3
  have hs := CompatibleActivitySplit.signed_error L F
  have ha := CompatibleActivitySplit.absolute_minus_positive L hL F
  have hi : 0 ≤ CompatibleActivitySplit.incompatibleAbsolute L F := sum_nonneg fun _ _ ↦ abs_nonneg _
  have hgap : |CompatibleActivitySplit.signed L F - CompatibleActivitySplit.absolute L F| ≤
      2 * CompatibleActivitySplit.incompatibleAbsolute L F := by
    apply abs_le.mpr
    obtain ⟨hl, hu⟩ := abs_le.mp hs
    constructor <;> linarith only [ha, hl, hu, hi]
  have htriangle := abs_sub_le (TripleJointPopulations.connectedJointMass G L)
    (CompatibleActivitySplit.signed L F) (CompatibleActivitySplit.absolute L F)
  have hj := signed_error G L hL
  have hb := incompatible_bound G L hL
  change |TripleJointPopulations.connectedJointMass G L - CompatibleActivitySplit.signed L F| ≤ _ at hj
  change CompatibleActivitySplit.incompatibleAbsolute L F ≤ _ at hb
  linarith only [htriangle, hgap, hj, hb]

end PaperP1.ConnectedTriplePositiveReduction
