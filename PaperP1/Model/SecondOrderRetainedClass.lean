module

public import PaperP1.Model.UnrestrictedRetainedExpansion
public import PaperP1.Model.CompatibleJointMajorant
public import PaperP1.Model.LocalRunRank
public import PaperP1.Probability.StoppedFiniteLaw

/-! # The all-pair retained class on the full heterogeneous ground has boundary nullity at most 2L -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondOrderRetainedClass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Model PaperP1.Model.InfiniteStarts

def Retained (G : Finset ℕ) (L : ℕ) (I : Finset ℕ) : Prop :=
  RetainedDependence.Retained (fun x ↦ squareClassSpace x L) (G.powersetCard 2) I

theorem hereditary (G : Finset ℕ) (L : ℕ) : Hereditary (Retained G L) :=
  RetainedDependence.hereditary (fun x ↦ squareClassSpace x L) _ (fun _e he ↦ (mem_powersetCard.mp he).2)

theorem empty (G : Finset ℕ) (L : ℕ) : Retained G L ∅ :=
  Or.inl (relativeNullityOn_empty (fun x ↦ squareClassSpace x L))

theorem pair (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) (he : e ∈ G.powersetCard 2) : Retained G L e :=
  Or.inr ⟨e, he, Subset.rfl, rfl⟩

theorem pair_nullity_le (L : ℕ) (e : Finset ℕ) (he : e.card = 2) (hpos : ∀ x ∈ e, 0 < x) :
    runRelativeNullity L e ≤ L := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp he
  change relativeNullityOn (fun x ↦ squareClassSpace x L) {x, y} ≤ L
  rw [RetainedNullity.nullity_pair_eq_intersection _ x y hxy]
  exact (Submodule.finrank_mono inf_le_left).trans
    (LocalRunRank.squareClass_rank_le x L (hpos x (by simp)))

theorem boundary_nullity {N L : ℕ} (hN : 0 < N) (G I : Finset ℕ) (hG : G ⊆ dyadicBlock N)
    (hIG : I ⊆ G) (hI : OrderedBoundary (Retained G L) I) :
    0 < runRelativeNullity L I ∧ runRelativeNullity L I ≤ 2 * L := by
  have hpos (x : ℕ) (hx : x ∈ G) : 0 < x := by have h := (mem_Ico.mp (hG hx)).1; omega
  have he : ∀ e ∈ G.powersetCard 2, (runRelativeNullity L e : ℝ) ≤ L := by
    intro e he
    exact_mod_cast pair_nullity_le L e (mem_powersetCard.mp he).2 (fun x hx ↦ hpos x ((mem_powersetCard.mp he).1 hx))
  have hlocal : ∀ x ∈ I, (Module.finrank F₂ (squareClassSpace x L) : ℝ) ≤ (L : ℝ) := by
    intro x hx
    exact_mod_cast LocalRunRank.squareClass_rank_le x L (hpos x (hIG hx))
  have h := RetainedDependence.boundary_nullity_bound (fun x ↦ squareClassSpace x L)
    (G.powersetCard 2) L L (by positivity) he I hI hlocal
  change 0 < runRelativeNullity L I ∧ (runRelativeNullity L I : ℝ) ≤ (L : ℝ) + L at h
  refine ⟨h.1, ?_⟩
  have hh : (runRelativeNullity L I : ℝ) ≤ 2 * L := by linarith only [h.2]
  exact_mod_cast hh

theorem boundary_subfamily_cap {N L : ℕ} (hN : 0 < N) (G I J : Finset ℕ) (hG : G ⊆ dyadicBlock N)
    (hIG : I ⊆ G) (hI : OrderedBoundary (Retained G L) I) (hJI : J ⊆ I) :
    runCompatibleNullity L J ≤ 2 * L :=
  (runCompatibleNullity_le_relative L J).trans
    ((relativeNullityOn_mono (fun x ↦ squareClassSpace x L) hJI).trans (boundary_nullity hN G I hG hIG hI).2)

theorem joint_expansion (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hI : Retained G L I) :
    infiniteJointMoment L I = (∏ x ∈ I, infiniteMarginal x L) +
      ∑ e ∈ I.powersetCard 2, infiniteCenteredCoefficient L e * ∏ x ∈ I \ e, infiniteMarginal x L :=
  UnrestrictedRetainedExpansion.joint_pair_expansion L hL _ (fun _e he ↦ (mem_powersetCard.mp he).2) I hI

end PaperP1.SecondOrderRetainedClass
