module

public import PaperP1.Model.BlockJointIntersection
public import PaperP1.Model.ConnectedTargetDependence
public import PaperP1.Model.WindowTargetHosts
public import PaperP1.Model.CompatibleNullityBound
public import PaperP1.Model.InfiniteTripleCancellation
public import PaperP1.Affine.DisjointBlockNullity

/-! # Exact finite crossing data for one actual window above an arbitrary source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OneTargetCrossing

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank

abbrev sourceSpace (e : Finset ℕ) (L : ℕ) := span (fun x ↦ squareClassSpace x L) e

def rank (e : Finset ℕ) (L z : ℕ) : ℕ :=
  Module.finrank F₂ ↥(squareClassSpace z L ⊓ sourceSpace e L)

theorem nullity_insert (e : Finset ℕ) (L z : ℕ) (hz : z ∉ e) :
    runRelativeNullity L (insert z e) = runRelativeNullity L e + rank e L z := by
  have hh := DisjointBlockNullity.union_nullity (fun x ↦ squareClassSpace x L) e {z}
    (disjoint_singleton_right.mpr hz)
  have hs : span (fun x ↦ squareClassSpace x L) {z} = squareClassSpace z L := by simp [span]
  rw [union_singleton, RetainedNullity.nullity_singleton, add_zero, hs, inf_comm] at hh
  exact hh

theorem connected_positive (e : Finset ℕ) (L z : ℕ) (he : e.Nonempty) (hz : z ∉ e)
    (hconn : ConnectedWindowFamilies.Connected L (insert z e)) : 0 < rank e L z := by
  have hsize : 2 ≤ (insert z e).card := by rw [card_insert_of_notMem hz]; have hh := he.card_pos; omega
  have hcross := ConnectedTargetDependence.every_target L (insert z e) hsize hconn (mem_insert_self z e)
  rw [erase_insert hz] at hcross
  apply Nat.pos_of_ne_zero
  intro hz
  exact hcross (Submodule.finrank_eq_zero.mp hz)

theorem mem_targets (G e : Finset ℕ) (L z : ℕ) (hz : z ∈ G) (hfresh : z ∉ e)
    (hpos : 0 < rank e L z) : z ∈ WindowTargetHosts.targets G L e := by
  classical
  apply mem_filter.mpr
  refine ⟨mem_sdiff.mpr ⟨hz, hfresh⟩, ?_⟩
  intro hbot
  have hh : rank e L z = 0 := by unfold rank; rw [hbot, finrank_bot]
  omega

theorem joint_upper (e : Finset ℕ) (L z : ℕ) (hL : 0 < L) (hz : z ∉ e) :
    infiniteJointMoment L (insert z e) ≤
      infiniteJointMoment L e * infiniteMarginal z L * (2 ^ rank e L z : ℝ) := by
  have hh := BlockJointIntersection.upper_bound L hL e {z} (disjoint_singleton_right.mpr hz)
  have hs : span (fun x ↦ squareClassSpace x L) {z} = squareClassSpace z L := by simp [span]
  rw [union_singleton, InfiniteTripleCancellation.singleton_joint, hs, inf_comm] at hh
  exact hh

end PaperP1.OneTargetCrossing
