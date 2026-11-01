module

public import PaperP1.Model.RetainedGoodEdges
public import PaperP1.Asymptotics.BoundaryCutoff

/-! # Actual joint probabilities and the positive mass of large boundary families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargeBoundaryMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model.InfiniteStarts
open PaperP1.RetainedGoodEdges

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def nominal (L : ℕ) : ℝ := (2 ^ L : ℝ)⁻¹

def families (H : ℝ) (N L K : ℕ) : Finset (Finset ℕ) :=
  (PaperP1.RegularStarts.regularStarts N L).powerset.filter
    fun I ↦ PaperP1.Algebra.OrderedBoundary (Retained H N L) I ∧ K < I.card

def mass (H : ℝ) (N L K : ℕ) : ℝ :=
  ∑ I ∈ families H N L K, (2 : ℝ) ^ I.card * infiniteJointMoment L I

theorem mem_families (H : ℝ) (N L K : ℕ) (I : Finset ℕ) :
    I ∈ families H N L K ↔ I ⊆ PaperP1.RegularStarts.regularStarts N L ∧
      PaperP1.Algebra.OrderedBoundary (Retained H N L) I ∧ K < I.card := by
  simp only [families, mem_filter, mem_powerset]

theorem joint_probability_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (I : Finset ℕ) (hreg : I ⊆ PaperP1.RegularStarts.regularStarts N L) :
    infiniteJointMoment L I ≤ nominal L ^ I.card * (2 : ℝ) ^ runRelativeNullity L I := by
  by_cases hq : 0 < infiniteJointMoment L I
  · have hcut : ∀ x ∈ I, x + L ≤ 2 * N + L := by
      intro x hx
      have hxdyad := (PaperP1.RegularStarts.mem_regularStarts.mp (hreg hx)).1
      have := (mem_Ico.mp hxdyad).2
      omega
    have hexact := infiniteJointMoment_exact_of_pos (2 * N + L) L I hL hcut hq
    have hprod : (∏ x ∈ I, infiniteMarginal x L) = nominal L ^ I.card := by
      calc
        _ = ∏ _x ∈ I, nominal L := by
          apply prod_congr rfl
          intro x hx
          have hxdyad := (PaperP1.RegularStarts.mem_regularStarts.mp (hreg hx)).1
          have hxpos : 0 < x := by have := (mem_Ico.mp hxdyad).1; omega
          exact PaperP1.RegularStarts.marginal_on_regular hxpos hL (hreg hx)
        _ = _ := by simp
    rw [hprod] at hexact
    exact hexact.le
  · exact (le_of_not_gt hq).trans (by unfold nominal; positivity)

theorem boundary_probability_bound {H : ℝ} {N L : ℕ} (hN : 2 ≤ N) (hL : 7 ≤ L)
    (I : Finset ℕ) (hreg : I ⊆ PaperP1.RegularStarts.regularStarts N L)
    (hI : PaperP1.Algebra.OrderedBoundary (Retained H N L) I) :
    infiniteJointMoment L I ≤ (2 : ℝ) ^ (3 * (L : ℝ) / 2) * nominal L ^ I.card := by
  have hloss := (finite_boundary_bound hN hL I hreg hI).2.2.le
  have hpower : (2 : ℝ) ^ runRelativeNullity L I ≤ (2 : ℝ) ^ (3 * (L : ℝ) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hloss
  calc
    _ ≤ nominal L ^ I.card * (2 : ℝ) ^ runRelativeNullity L I := joint_probability_bound hN (by omega) I hreg
    _ ≤ nominal L ^ I.card * (2 : ℝ) ^ (3 * (L : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hpower (by unfold nominal; positivity)
    _ = _ := mul_comm _ _

theorem rank_budget_majorant {H : ℝ} {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (K : ℕ)
    (R : ℝ) (hbudget : ∀ I ∈ families H N L K, (runRelativeNullity L I : ℝ) ≤ R) :
    mass H N L K ≤ (2 : ℝ) ^ R *
      PaperP1.LargeSubsetWeights.weightSum (PaperP1.RegularStarts.regularStarts N L) (2 * nominal L) K := by
  have hsubset : families H N L K ⊆
      PaperP1.LargeSubsetWeights.subsets (PaperP1.RegularStarts.regularStarts N L) K := by
    intro I hI
    obtain ⟨hreg, _, hcard⟩ := (mem_families H N L K I).mp hI
    exact mem_filter.mpr ⟨mem_powerset.mpr hreg, hcard⟩
  unfold mass
  calc
    _ ≤ ∑ I ∈ families H N L K, (2 : ℝ) ^ R * (2 * nominal L) ^ I.card := by
      apply sum_le_sum
      intro I hI
      obtain ⟨hreg, _, _⟩ := (mem_families H N L K I).mp hI
      have hpower : (2 : ℝ) ^ runRelativeNullity L I ≤ (2 : ℝ) ^ R := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hbudget I hI)
      have hq : infiniteJointMoment L I ≤ (2 : ℝ) ^ R * nominal L ^ I.card := by
        exact (joint_probability_bound hN hL I hreg).trans (by
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left hpower (by unfold nominal; positivity : 0 ≤ nominal L ^ I.card))
      calc
        _ ≤ (2 : ℝ) ^ I.card * ((2 : ℝ) ^ R * nominal L ^ I.card) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
        _ = _ := by rw [mul_pow]; ring
    _ ≤ ∑ I ∈ PaperP1.LargeSubsetWeights.subsets (PaperP1.RegularStarts.regularStarts N L) K,
        (2 : ℝ) ^ R * (2 * nominal L) ^ I.card :=
      sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ ↦ by unfold nominal; positivity)
    _ = _ := by rw [PaperP1.LargeSubsetWeights.weightSum, mul_sum]

theorem mass_majorant {H : ℝ} {N L : ℕ} (hN : 2 ≤ N) (hL : 7 ≤ L) (K : ℕ) :
    mass H N L K ≤ (2 : ℝ) ^ (3 * (L : ℝ) / 2) *
      PaperP1.LargeSubsetWeights.weightSum (PaperP1.RegularStarts.regularStarts N L) (2 * nominal L) K := by
  apply rank_budget_majorant hN (by omega) K
  intro I hI
  obtain ⟨hreg, hboundary, _⟩ := (mem_families H N L K I).mp hI
  exact (finite_boundary_bound hN hL I hreg hboundary).2.2.le

theorem precise_nullity_majorant {H : ℝ} {N L : ℕ} (hN : 2 ≤ N) (hL : 7 ≤ L) (K : ℕ) :
    mass H N L K ≤ (2 : ℝ) ^ (4 * (L : ℝ) / 3 + 1) *
      PaperP1.LargeSubsetWeights.weightSum (PaperP1.RegularStarts.regularStarts N L) (2 * nominal L) K := by
  apply rank_budget_majorant hN (by omega) K
  intro I hI
  obtain ⟨hreg, hboundary, _⟩ := (mem_families H N L K I).mp hI
  exact (finite_boundary_bound hN hL I hreg hboundary).2.1

theorem cutoff_mass_bound {H : ℝ} {N L : ℕ} (hN : 2 ≤ N) (hL : 7 ≤ L)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (hmean : ((PaperP1.RegularStarts.regularStarts N L).card : ℝ) * nominal L ≤ Λ) :
    mass H N L (PaperP1.BoundaryCutoff.cutoff Λ hΛ N) ≤
      (2 : ℝ) ^ (3 * (L : ℝ) / 2) * (N : ℝ) ^ (-3 : ℝ) := by
  exact (mass_majorant hN hL _).trans (mul_le_mul_of_nonneg_left
    (PaperP1.BoundaryCutoff.powerset_tail_bound _ (nominal L) Λ hΛ N (by omega)
      (by unfold nominal; positivity) hmean) (Real.rpow_nonneg (by norm_num) _))

theorem precise_cutoff_mass_bound {H : ℝ} {N L : ℕ} (hN : 2 ≤ N) (hL : 7 ≤ L)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (hmean : ((PaperP1.RegularStarts.regularStarts N L).card : ℝ) * nominal L ≤ Λ) :
    mass H N L (PaperP1.BoundaryCutoff.cutoff Λ hΛ N) ≤
      (2 : ℝ) ^ (4 * (L : ℝ) / 3 + 1) * (N : ℝ) ^ (-3 : ℝ) := by
  exact (precise_nullity_majorant hN hL _).trans (mul_le_mul_of_nonneg_left
    (PaperP1.BoundaryCutoff.powerset_tail_bound _ (nominal L) Λ hΛ N (by omega)
      (by unfold nominal; positivity) hmean) (Real.rpow_nonneg (by norm_num) _))

end PaperP1.LargeBoundaryMass
