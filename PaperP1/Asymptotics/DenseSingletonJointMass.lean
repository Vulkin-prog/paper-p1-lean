module

public import PaperP1.Asymptotics.DenseSingletonWeakTargets
public import PaperP1.Asymptotics.StrongAlignedDenseJointMass

/-! # Every dense minimal pair crossing above one full actual source has joint cost N⁻¹ -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseSingletonJointMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.TwoTargetPrimitiveData

theorem uniform_joint (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e : Finset ℕ, e.card = 1 → e ⊆ dyadicBlock N → ∀ F : Finset (ℕ × ℕ),
      (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧ p.1 ≠ p.2 ∧ p.1 ∉ e ∧ p.2 ∉ e) →
      (∀ p ∈ F, ∀ B : Finset ℕ, B ⊂ {p.1, p.2} →
        Disjoint (sourceSpace e L) (span (fun x ↦ squareClassSpace x L) B)) →
      (∀ p ∈ F, η * L ≤ (Module.finrank F₂ ↥(sourceSpace e L ⊓
        span (fun x ↦ squareClassSpace x L) {p.1, p.2}) : ℝ)) →
      (∑ p ∈ F, infiniteJointMoment L (TwoTargetFamilyCover.family e p)) ≤
        infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨NN, _hNN, hn⟩ := DenseSingletonNonalignedTargets.uniform_joint C η (ε / 2) hη (by positivity)
  obtain ⟨NW, _hNW, hw⟩ := DenseSingletonWeakTargets.uniform_joint C η (ε / 2) hη (by positivity)
  obtain ⟨NS, _hNS, hs⟩ := StrongAlignedDenseJointMass.uniform_joint 1 (η / 64) C η (ε / 2)
    (by positivity) hη (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 3 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NN + NW + NS + NA, by omega, ?_⟩
  intro N hN L hband e hecard heG F hF hproper hdense
  obtain ⟨x, rfl⟩ := card_eq_one.mp hecard
  have hx : x ∈ dyadicBlock N := heG (mem_singleton_self x)
  have hsource : sourceSpace {x} L = squareClassSpace x L := by simp [sourceSpace, span]
  rw [InfiniteTripleCancellation.singleton_joint]
  let FN := F.filter fun p ↦ ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L
  let A := F \ FN
  let FW := A.filter fun p ↦
    (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ (η / 64) * L
  let FS := A \ FW
  have hFN : FN ⊆ F := filter_subset _ _
  have hA : A ⊆ F := sdiff_subset
  have hFW : FW ⊆ F := (filter_subset _ _).trans hA
  have hFS : FS ⊆ F := sdiff_subset.trans hA
  have haligned (p : ℕ × ℕ) (hp : p ∈ A) : CompressedTargetAlignment.Aligned 1 p.1 p.2 L := by
    by_contra hh
    exact (mem_sdiff.mp hp).2 (mem_filter.mpr ⟨(mem_sdiff.mp hp).1, hh⟩)
  have hdata (p : ℕ × ℕ) (hp : p ∈ F) : p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧
      p.1 ≠ p.2 ∧ p.1 ≠ x ∧ p.2 ≠ x := by
    have hh := hF p hp
    exact ⟨hh.1, hh.2.1, hh.2.2.1,
      by simpa only [mem_singleton] using hh.2.2.2.1,
      by simpa only [mem_singleton] using hh.2.2.2.2⟩
  have hdis (p : ℕ × ℕ) (hp : p ∈ F) :
      Disjoint (squareClassSpace x L) (squareClassSpace p.1 L) ∧
      Disjoint (squareClassSpace x L) (squareClassSpace p.2 L) ∧
      η * L ≤ (Module.finrank F₂ ↥(squareClassSpace x L ⊓
        span (fun y ↦ squareClassSpace y L) {p.1, p.2}) : ℝ) := by
    have hc : ({p.1, p.2} : Finset ℕ).card = 2 := card_pair (hF p hp).2.2.1
    have hcuts := MinimalSpanCrossing.disjoint_singletons (fun y ↦ squareClassSpace y L)
      (sourceSpace {x} L) {p.1, p.2} (by omega) (hproper p hp)
    rw [hsource] at hcuts
    exact ⟨hcuts p.1 (mem_insert_self _ _), hcuts p.2 (mem_insert_of_mem (mem_singleton_self _)),
      by
        have hh := hdense p hp
        rw [hsource] at hh
        exact hh⟩
  have hNmass := hn N (by omega) L hband x hx FN (fun p hp ↦ hdata p (hFN hp))
    (fun _ hp ↦ (mem_filter.mp hp).2) (fun p hp ↦ hdis p (hFN hp))
  have hWmass := hw N (by omega) L hband x hx FW (fun p hp ↦ hdata p (hFW hp))
    (fun p hp ↦ ⟨haligned p (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩)
    (fun p hp ↦ hdis p (hFW hp))
  have hSmass := hs N (by omega) L hband {x} (by simp) heG FS (by
    intro p hp
    have hh := hF p (hFS hp)
    have hstrong : (η / 64) * L <
        (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) :=
      lt_of_not_ge (fun h ↦ (mem_sdiff.mp hp).2 (mem_filter.mpr ⟨(mem_sdiff.mp hp).1, h⟩))
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2,
      haligned p (mem_sdiff.mp hp).1, hstrong, hdense p (hFS hp)⟩)
    (fun p hp ↦ hproper p (hFS hp))
  rw [InfiniteTripleCancellation.singleton_joint] at hSmass
  have hpart₁ := sum_sdiff (f := fun p ↦ infiniteJointMoment L (TwoTargetFamilyCover.family {x} p)) hFN
  have hpart₂ := sum_sdiff (f := fun p ↦ infiniteJointMoment L (TwoTargetFamilyCover.family {x} p))
    (show FW ⊆ A from filter_subset _ _)
  change (∑ p ∈ A, _) + (∑ p ∈ FN, _) = _ at hpart₁
  change (∑ p ∈ FS, _) + (∑ p ∈ FW, _) = _ at hpart₂
  have hfactor : 3 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert ha N (by omega) using 1
    congr 1
    ring
  have hscaled := mul_le_mul_of_nonneg_left hfactor (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  nlinarith only [hNmass, hWmass, hSmass, hpart₁, hpart₂, hscaled]

end PaperP1.DenseSingletonJointMass
