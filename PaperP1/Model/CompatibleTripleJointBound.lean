module

public import PaperP1.Model.TripleJointPopulations
public import PaperP1.Model.CompatibleNullityBound
public import PaperP1.Model.TripleActivityConnected
public import PaperP1.Model.InfiniteTripleCancellation

/-! # A finite actual-joint majorant for the positive triple activity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompatibleTripleJointBound

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

local instance compatibleTripleJointBoundDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem marginals_pos_of_joint (L : ℕ) (I : Finset ℕ)
    (hq : 0 < infiniteJointMoment L I) : ∀ x ∈ I, 0 < infiniteMarginal x L := by
  intro x hx
  have hsub : ({x} : Finset ℕ) ⊆ I := singleton_subset_iff.mpr hx
  have h := hq.trans_le (MissingBlockProbabilities.infiniteJointMoment_antitone L hsub)
  simpa only [InfiniteTripleCancellation.singleton_joint] using h

theorem centered_compatible_bound (L : ℕ) (I : Finset ℕ) (hL : 0 < L)
    (hq : 0 < infiniteJointMoment L I) :
    |infiniteCenteredCoefficient L I| ≤ (2 ^ I.card : ℝ) * infiniteJointMoment L I := by
  let M := I.sup fun x ↦ x + L
  have hcut : ∀ x ∈ I, x + L ≤ M := fun x hx ↦ le_sup (f := fun x ↦ x + L) hx
  have h := infinite_centered_compatible_nullity_bound L I hL (marginals_pos_of_joint L I hq)
  rw [runCompatibleNullity_eq_of_positive_joint L I hq] at h
  rw [infiniteJointMoment_exact_of_pos M L I hL hcut hq]
  simpa only [runRelativeNullity, mul_assoc] using h

theorem positive_triple_activity_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    CompatibleActivitySplit.positive L (G.powersetCard 3) ≤
      8 * TripleJointPopulations.connectedJointMass G L := by
  unfold CompatibleActivitySplit.positive TripleJointPopulations.connectedJointMass
    ConnectedWindowFamilies.connectedFamilies
  rw [sum_filter, mul_sum]
  simp only [sum_filter]
  apply sum_le_sum
  intro I hI
  have hcard := (mem_powersetCard.mp hI).2
  by_cases hq : 0 < infiniteJointMoment L I
  · by_cases hconn : ConnectedWindowFamilies.Connected L I
    · simp only [hq, hconn, ite_true]
      have h := centered_compatible_bound L I hL hq
      rw [hcard] at h
      norm_num only [Nat.reducePow, Nat.cast_ofNat] at h
      exact (le_abs_self _).trans h
    · have hz := TripleActivityConnected.coefficient_zero_of_disconnected L hL I hcard
        (marginals_pos_of_joint L I hq) hconn
      simp only [hq, hconn, hz, ite_true, ite_false, le_refl]
  · simp only [hq, ite_false]
    by_cases hconn : ConnectedWindowFamilies.Connected L I
    · simp only [hconn, ite_true]
      exact mul_nonneg (by norm_num) (infiniteJointMoment_nonneg L I)
    · simp only [hconn, ite_false, le_refl]

end PaperP1.CompatibleTripleJointBound
