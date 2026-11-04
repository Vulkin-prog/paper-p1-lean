module

public import PaperP1.Combinatorics.SequentialBranchingPaths
public import PaperP1.Model.JointBranchingEvents
public import PaperP1.Model.OneTargetCrossing
public import PaperP1.Arithmetic.IntersectionExceptional
public import PaperP1.Affine.RetainedDependence

/-! # Actual retained branching paths preserve the source relation kernel at every order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SequentialRetainedWindows

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.BranchingExceptional PaperP1.OldValuePrimeBudget PaperP1.SequentialBranchingPaths

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def next (N L : ℕ) (A : Finset ℕ) : Finset ℕ :=
  dyadicBlock N \ (A ∪ badStarts N L (rawValues A L))

def paths (N L : ℕ) (A : Finset ℕ) (k : ℕ) : Finset (List ℕ) :=
  SequentialBranchingPaths.paths (next N L) A k

def mass (N L : ℕ) (A : Finset ℕ) (k : ℕ) : ℝ :=
  ∑ xs ∈ paths N L A k, infiniteJointMoment L (old A xs)

theorem mem_next (N L z : ℕ) (A : Finset ℕ) : z ∈ next N L A ↔
    z ∈ dyadicBlock N ∧ z ∉ A ∧ z ∉ badStarts N L (rawValues A L) := by
  simp only [next, mem_sdiff, mem_union, not_or]

theorem next_subset (N L : ℕ) (A : Finset ℕ) : next N L A ⊆ dyadicBlock N \ A := by
  intro z hz
  have hh := (mem_next N L z A).mp hz
  exact mem_sdiff.mpr ⟨hh.1, hh.2.1⟩

theorem independent_conclusion {N L : ℕ} (hN : 2 ≤ N) (A : Finset ℕ) (hA : A ⊆ dyadicBlock N) :
    FixedWindowBranching.IndependentConclusion N L A (A ∪ badStarts N L (rawValues A L)) := by
  intro z hz hnot
  exact FixedWindowBranching.retained_independent hN hA z hz
    (fun hb ↦ hnot (mem_union_right _ hb))

theorem data {N L : ℕ} (A : Finset ℕ) (hA : A ⊆ dyadicBlock N) (k : ℕ)
    (xs : List ℕ) (hxs : xs ∈ paths N L A k) :
    xs.length = k ∧ xs.Nodup ∧ Disjoint A xs.toFinset ∧ old A xs ⊆ dyadicBlock N :=
  SequentialBranchingPaths.data _ _ _ hA (fun S _ ↦ next_subset N L S) k xs hxs

theorem probability_exact {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (A : Finset ℕ) (hA : A ⊆ dyadicBlock N) (k : ℕ) (xs : List ℕ) (hxs : xs ∈ paths N L A k) :
    infiniteJointMoment L (old A xs) = ((2 ^ L : ℝ)⁻¹) ^ k * infiniteJointMoment L A := by
  apply SequentialBranchingPaths.probability_exact (dyadicBlock N) (next N L) A hA
    (fun S _ ↦ next_subset N L S) (infiniteJointMoment L) ((2 ^ L : ℝ)⁻¹) _ k xs hxs
  intro S hS z hz
  have hh := (mem_next N L z S).mp hz
  exact JointBranchingEvents.retained_joint_factor hN hL hS hh.1 hh.2.2

theorem mass_exact {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (A : Finset ℕ) (hA : A ⊆ dyadicBlock N) (k : ℕ) :
    mass N L A k = (paths N L A k).card * (((2 ^ L : ℝ)⁻¹) ^ k * infiniteJointMoment L A) := by
  calc
    _ = ∑ _xs ∈ paths N L A k, ((2 ^ L : ℝ)⁻¹) ^ k * infiniteJointMoment L A :=
      sum_congr rfl (fun xs hxs ↦ probability_exact hN hL A hA k xs hxs)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem rank_zero {N L z : ℕ} (hN : 2 ≤ N) (A : Finset ℕ) (hA : A ⊆ dyadicBlock N)
    (hz : z ∈ next N L A) : OneTargetCrossing.rank A L z = 0 := by
  have hh := (mem_next N L z A).mp hz
  have hraw := IntersectionExceptional.span_le_raw A L (by
    intro x hx
    have hp := (mem_Ico.mp (hA hx)).1
    omega)
  have hbot : squareClassSpace z L ⊓ OneTargetCrossing.sourceSpace A L = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    apply (Submodule.mem_bot F₂).mpr
    by_contra hne
    exact hh.2.2 (IntersectionExceptional.of_intersection hN hh.1 hne hv.1 (hraw hv.2))
  change Module.finrank F₂ ↥(squareClassSpace z L ⊓ OneTargetCrossing.sourceSpace A L) = 0
  rw [hbot, finrank_bot]

theorem compression {N L : ℕ} (hN : 2 ≤ N) (A : Finset ℕ) (hA : A ⊆ dyadicBlock N)
    (k : ℕ) (xs : List ℕ) (hxs : xs ∈ paths N L A k) :
    RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) A (old A xs) := by
  refine ⟨subset_union_left, ?_⟩
  change runRelativeNullity L (old A xs) = runRelativeNullity L A
  induction k generalizing xs with
  | zero =>
    have heq : xs = [] := mem_singleton.mp hxs
    subst xs
    simp only [old, List.toFinset_nil, union_empty]
  | succ k ih =>
    obtain ⟨ys, hys, himage⟩ := mem_biUnion.mp hxs
    obtain ⟨z, hz, rfl⟩ := mem_image.mp himage
    have hsub := (data A hA k ys hys).2.2.2
    have hfresh := ((mem_next N L z (old A ys)).mp hz).2.1
    rw [old_cons, OneTargetCrossing.nullity_insert _ L z hfresh, rank_zero hN _ hsub hz, add_zero]
    exact ih ys hys

theorem unique_dependent_pair {N L : ℕ} (hN : 2 ≤ N) (e : Finset ℕ) (he : e.card = 2)
    (heG : e ⊆ dyadicBlock N) (hdep : 0 < runRelativeNullity L e)
    (k : ℕ) (xs : List ℕ) (hxs : xs ∈ paths N L e k) :
    ∀ f : Finset ℕ, f ⊆ old e xs → f.card = 2 → 0 < runRelativeNullity L f → f = e := by
  have hc := compression hN e heG k xs hxs
  have hnot : relativeNullityOn (fun x ↦ squareClassSpace x L) (old e xs) ≠ 0 := by
    have hh := hc.2
    change runRelativeNullity L (old e xs) = runRelativeNullity L e at hh
    change runRelativeNullity L (old e xs) ≠ 0
    omega
  obtain ⟨f, hf, _hfc, _hfpos, huniq⟩ := RetainedDependence.dependent_pair_unique
    (fun x ↦ squareClassSpace x L) {e} (by intro f hf; simpa only [mem_singleton.mp hf] using he)
    (old e xs) (Or.inr ⟨e, mem_singleton_self _, hc⟩) hnot
  rw [mem_singleton.mp hf] at huniq
  exact huniq

theorem next_card_lower {N L m : ℕ} (A : Finset ℕ) (hA : A ⊆ dyadicBlock N) (hcard : A.card ≤ m)
    (D : ℝ) (hbad : ((badStarts N L (rawValues A L)).card : ℝ) ≤ D) :
    (N : ℝ) - (D + m) ≤ (next N L A).card := by
  have hsub : A ∪ badStarts N L (rawValues A L) ⊆ dyadicBlock N :=
    union_subset hA (badStarts_subset _ _ _)
  have hc := card_sdiff_add_card_eq_card hsub
  rw [dyadicBlock_card] at hc
  have hcr : ((next N L A).card : ℝ) + (A ∪ badStarts N L (rawValues A L)).card = N := by exact_mod_cast hc
  have hu : ((A ∪ badStarts N L (rawValues A L)).card : ℝ) ≤ A.card + (badStarts N L (rawValues A L)).card := by
    exact_mod_cast card_union_le A (badStarts N L (rawValues A L))
  have hAm : (A.card : ℝ) ≤ m := by exact_mod_cast hcard
  linarith only [hcr, hu, hbad, hAm]

end PaperP1.SequentialRetainedWindows
