module

public import PaperP1.Model.PrimitiveWindowMass
public import PaperP1.Model.CompatibleNullityBound
public import PaperP1.Model.WindowTargetHosts
public import PaperP1.Probability.PositionalCompoundPoisson

/-! # Incident pair probability is controlled by the actual one-source target mass

No bound on the graph degree is needed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IncidentPairMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

local instance incidentPairMassDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem finite_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (E : Finset (Finset ℕ))
    (K : ℝ) (hK : 0 ≤ K)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2 ∧ 0 < runRelativeNullity L e ∧ (2 ^ runRelativeNullity L e : ℝ) ≤ K)
    (x : ℕ) :
    PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x ≤
      (infiniteMarginal x L * K) * ∑ y ∈ WindowTargetHosts.targets G L {x}, infiniteMarginal y L := by
  classical
  let Y := G.filter fun y ↦ y ≠ x ∧ ({x, y} : Finset ℕ) ∈ E
  let EX := E.filter fun e ↦ x ∈ e
  have hcover : EX ⊆ Y.image (fun y ↦ ({x, y} : Finset ℕ)) := by
    intro e he
    obtain ⟨heE, hx⟩ := mem_filter.mp he
    obtain ⟨heG, hcard, _hpos, _hpower⟩ := hE e heE
    have hcarderase : (e.erase x).card = 1 := by rw [card_erase_of_mem hx, hcard]
    obtain ⟨y, hy⟩ := card_eq_one.mp hcarderase
    have hyerase : y ∈ e.erase x := by rw [hy]; exact mem_singleton_self y
    have heq : ({x, y} : Finset ℕ) = e := by rw [← hy, insert_erase hx]
    have hyY : y ∈ Y := mem_filter.mpr ⟨heG (mem_erase.mp hyerase).2, (mem_erase.mp hyerase).1, heq.symm ▸ heE⟩
    exact mem_image.mpr ⟨y, hyY, heq⟩
  have hYtargets : Y ⊆ WindowTargetHosts.targets G L {x} := by
    intro y hy
    obtain ⟨hyG, hyx, heE⟩ := mem_filter.mp hy
    have hpos := (hE _ heE).2.2.1
    have hxy : x ≠ y := hyx.symm
    rw [runRelativeNullity, RetainedNullity.nullity_pair_eq_intersection _ x y hxy] at hpos
    apply mem_filter.mpr
    refine ⟨mem_sdiff.mpr ⟨hyG, by simpa only [mem_singleton] using hyx⟩, ?_⟩
    have hspan : SubspaceFamilyRank.span (fun z ↦ squareClassSpace z L) {x} = squareClassSpace x L := by
      simp [SubspaceFamilyRank.span]
    change squareClassSpace y L ⊓ SubspaceFamilyRank.span (fun z ↦ squareClassSpace z L) {x} ≠ ⊥
    rw [hspan, inf_comm]
    intro hbot
    rw [hbot, finrank_bot] at hpos
    omega
  have hpoint (y : ℕ) (hy : y ∈ Y) : infiniteJointMoment L {x, y} ≤
      (infiniteMarginal x L * K) * infiniteMarginal y L := by
    obtain ⟨_hyG, hyx, heE⟩ := mem_filter.mp hy
    have hh := PrimitiveWindowMass.joint_le_weight L hL {x, y}
    change infiniteJointMoment L {x, y} ≤
      (∏ z ∈ ({x, y} : Finset ℕ), infiniteMarginal z L) * (2 ^ runRelativeNullity L {x, y} : ℝ) at hh
    rw [prod_pair hyx.symm] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (hE _ heE).2.2.2
      (mul_nonneg (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
        (MissingBlockProbabilities.infiniteMarginal_nonneg y L))).trans_eq (by ring))
  have hinc : PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x =
      ∑ e ∈ EX, infiniteJointMoment L e := by
    rw [PositionalCompoundPoisson.incidence, show EX = E.filter (fun e ↦ x ∈ e) from rfl, sum_filter]
    congr!
  calc
    _ = ∑ e ∈ EX, infiniteJointMoment L e := hinc
    _ ≤ ∑ e ∈ Y.image (fun y ↦ ({x, y} : Finset ℕ)), infiniteJointMoment L e :=
      sum_le_sum_of_subset_of_nonneg hcover (fun e _ _ ↦ infiniteJointMoment_nonneg L e)
    _ ≤ ∑ y ∈ Y, infiniteJointMoment L {x, y} :=
      sum_image_le_of_nonneg (fun e _ ↦ infiniteJointMoment_nonneg L e)
    _ ≤ ∑ y ∈ Y, (infiniteMarginal x L * K) * infiniteMarginal y L := sum_le_sum hpoint
    _ = (infiniteMarginal x L * K) * ∑ y ∈ Y, infiniteMarginal y L := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg hYtargets (fun y _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg y L))
      (mul_nonneg (MissingBlockProbabilities.infiniteMarginal_nonneg x L) hK)

end PaperP1.IncidentPairMass
