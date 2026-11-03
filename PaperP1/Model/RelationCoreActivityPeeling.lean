module

public import PaperP1.Model.RelationCoreWitnesses
public import PaperP1.Model.CompatibleNullityBound
public import PaperP1.Model.PositiveMarginalRestriction

/-! # The actual centered activity is charged to a constructed compatible relation core -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelationCoreActivityPeeling

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model.InfiniteStarts
  PaperP1.RelationCoreWitnesses

theorem compatible_majorant (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    |infiniteCenteredCoefficient L I| ≤ (2 ^ I.card : ℝ) *
      (∏ x ∈ I, infiniteMarginal x L) * (2 ^ runCompatibleNullity L I : ℝ) := by
  classical
  by_cases hp : ∀ x ∈ I, 0 < infiniteMarginal x L
  · exact infinite_centered_compatible_nullity_bound L I hL hp
  · push Not at hp
    obtain ⟨x, hx, hnot⟩ := hp
    have hz : infiniteMarginal x L = 0 := le_antisymm hnot
      (PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    rw [PaperP1.PositiveMarginalRestriction.zero_centered L I x hx hz, abs_zero]
    exact mul_nonneg (mul_nonneg (by positivity)
      (prod_nonneg fun x _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L))
      (by positivity)

theorem peeling_bound (L : ℕ) (hL : 0 < L) (I A D : Finset ℕ) (k : ℕ)
    (hAI : A ⊆ I) (hqA : 0 < infiniteJointMoment L A)
    (hmax : runCompatibleNullity L I = runRelativeNullity L A)
    (htrace : PaperP1.RelationCorePeeling.Trace (fun x ↦ squareClassSpace x L) k A D) :
    |infiniteCenteredCoefficient L I| ≤ (2 ^ I.card : ℝ) *
      (2 ^ (k * (I.card - D.card)) : ℝ) *
      (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D := by
  have hDA := PaperP1.RelationCorePeeling.trace_subset _ htrace
  have hDI := hDA.trans hAI
  have hqD : 0 < infiniteJointMoment L D := hqA.trans_le
    (PaperP1.MissingBlockProbabilities.infiniteJointMoment_antitone L hDA)
  have hbudget := PaperP1.RelationCorePeeling.trace_nullity_budget _ htrace
  have hcost : k * (A.card - D.card) ≤ k * (I.card - D.card) :=
    Nat.mul_le_mul_left k (Nat.sub_le_sub_right (card_le_card hAI) D.card)
  have hrank : runCompatibleNullity L I ≤ runRelativeNullity L D + k * (I.card - D.card) := by
    rw [hmax]
    change runRelativeNullity L A ≤ runRelativeNullity L D + k * (A.card - D.card) at hbudget
    omega
  have hpow : (2 ^ runCompatibleNullity L I : ℝ) ≤
      (2 ^ runRelativeNullity L D : ℝ) * 2 ^ (k * (I.card - D.card)) := by
    simpa only [pow_add] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hrank
  have hnonneg : 0 ≤ (2 ^ I.card : ℝ) * ∏ x ∈ I, infiniteMarginal x L :=
    mul_nonneg (by positivity)
      (prod_nonneg fun x _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have hprod : (∏ x ∈ D, infiniteMarginal x L) * (∏ x ∈ I \ D, infiniteMarginal x L) =
      ∏ x ∈ I, infiniteMarginal x L := by
    rw [mul_comm, prod_sdiff hDI]
  let M := D.sup fun x ↦ x + L
  have hcut : ∀ x ∈ D, x + L ≤ M := fun x hx ↦ le_sup (f := fun x ↦ x + L) hx
  calc
    _ ≤ (2 ^ I.card : ℝ) * (∏ x ∈ I, infiniteMarginal x L) *
        (2 ^ runCompatibleNullity L I : ℝ) := compatible_majorant L hL I
    _ ≤ (2 ^ I.card : ℝ) * (∏ x ∈ I, infiniteMarginal x L) *
        ((2 ^ runRelativeNullity L D : ℝ) * 2 ^ (k * (I.card - D.card))) :=
      mul_le_mul_of_nonneg_left hpow hnonneg
    _ = _ := by
      rw [infiniteJointMoment_exact_of_pos M L D hL hcut hqD, ← hprod]
      unfold runRelativeNullity
      ring

theorem exists_ten_core_bound (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    ∃ D ⊆ I, Core 10 L D ∧ 0 < infiniteJointMoment L D ∧
      runCompatibleNullity L I ≤ runRelativeNullity L D + 8 * (I.card - D.card) ∧
      |infiniteCenteredCoefficient L I| ≤ (2 ^ I.card : ℝ) *
        (2 ^ (8 * (I.card - D.card)) : ℝ) *
        (∏ x ∈ I \ D, infiniteMarginal x L) * infiniteJointMoment L D := by
  obtain ⟨A, hAI, hqA, hmax⟩ := runCompatibleNullity_attained L I
  obtain ⟨D, htrace, hstop⟩ := PaperP1.RelationCorePeeling.exists_terminal_trace
    (fun x ↦ squareClassSpace x L) A 8
  have hDA := PaperP1.RelationCorePeeling.trace_subset _ htrace
  have hbudget := PaperP1.RelationCorePeeling.trace_nullity_budget _ htrace
  have hcost : 8 * (A.card - D.card) ≤ 8 * (I.card - D.card) :=
    Nat.mul_le_mul_left 8 (Nat.sub_le_sub_right (card_le_card hAI) D.card)
  refine ⟨D, hDA.trans hAI, ?_, ?_, ?_, peeling_bound L hL I A D 8 hAI hqA hmax htrace⟩
  · intro x hx
    have h := hstop x hx
    omega
  · exact hqA.trans_le (PaperP1.MissingBlockProbabilities.infiniteJointMoment_antitone L hDA)
  · rw [hmax]
    change runRelativeNullity L A ≤ runRelativeNullity L D + 8 * (A.card - D.card) at hbudget
    omega

end PaperP1.RelationCoreActivityPeeling
