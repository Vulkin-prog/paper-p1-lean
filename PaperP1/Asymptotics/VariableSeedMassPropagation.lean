module

public import PaperP1.Asymptotics.UnorderedSeedMassPropagation
public import PaperP1.Combinatorics.GraphStarWeights
public import Mathlib.Order.Filter.Finite

/-! # A single actual seed population of varying bounded sizes propagates with only the fixed target factorial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.VariableSeedMassPropagation

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_mass (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ S : Finset (Finset ℕ), (∀ D ∈ S, D ⊆ dyadicBlock N ∧ 1 ≤ D.card ∧ D.card ≤ r) →
      ∀ T : Finset (Finset ℕ),
      (∀ I ∈ T, I ⊆ dyadicBlock N ∧ I.card = r ∧ ∃ D ∈ S, D ⊆ I) →
      (∑ I ∈ T, infiniteJointMoment L I) ≤
        (r.factorial : ℝ) * (N : ℝ) ^ ε * ∑ D ∈ S, infiniteJointMoment L D := by
  classical
  have heach (s : ℕ) (hs : s ∈ Icc 1 r) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ S : Finset (Finset ℕ), (∀ D ∈ S, D ⊆ dyadicBlock N ∧ D.card = s) →
      ∀ T : Finset (Finset ℕ),
      (∀ I ∈ T, I ⊆ dyadicBlock N ∧ I.card = r ∧ ∃ D ∈ S, D ⊆ I) →
      (∑ I ∈ T, infiniteJointMoment L I) ≤
        (r.factorial : ℝ) * (N : ℝ) ^ ε * ∑ D ∈ S, infiniteJointMoment L D := by
    obtain ⟨N₀, h⟩ := UnorderedSeedMassPropagation.uniform_mass s (mem_Icc.mp hs).1 (r - s) C ε hε
    have hsr : s + (r - s) = r := by have h := (mem_Icc.mp hs).2; omega
    rw [hsr] at h
    exact eventually_atTop.mpr ⟨N₀, h⟩
  obtain ⟨N₀, hp⟩ := eventually_atTop.mp ((Finset.eventually_all (Icc 1 r)).mpr heach)
  refine ⟨N₀, ?_⟩
  intro N hN L hL hband S hS T hT
  let source := fun s : ℕ ↦ S.filter fun D ↦ D.card = s
  let target := fun s : ℕ ↦ T.filter fun I ↦ ∃ D ∈ source s, D ⊆ I
  have hsub : T ⊆ (Icc 1 r).biUnion target := by
    intro I hI
    obtain ⟨D, hD, hDI⟩ := (hT I hI).2.2
    exact mem_biUnion.mpr ⟨D.card, mem_Icc.mpr ⟨(hS D hD).2.1, (hS D hD).2.2⟩,
      mem_filter.mpr ⟨hI, D, mem_filter.mpr ⟨hD, rfl⟩, hDI⟩⟩
  have hcell (s : ℕ) (hs : s ∈ Icc 1 r) :
      (∑ I ∈ target s, infiniteJointMoment L I) ≤
        (r.factorial : ℝ) * (N : ℝ) ^ ε * ∑ D ∈ source s, infiniteJointMoment L D := by
    apply hp N hN s hs L hL hband (source s)
    · intro D hD
      exact ⟨(hS D (mem_filter.mp hD).1).1, (mem_filter.mp hD).2⟩
    · intro I hI
      obtain ⟨hIT, hseed⟩ := mem_filter.mp hI
      exact ⟨(hT I hIT).1, (hT I hIT).2.1, hseed⟩
  have hsplit := sum_fiberwise_of_maps_to (s := S) (t := Icc 1 r) (g := fun D : Finset ℕ ↦ D.card)
    (fun D hD ↦ mem_Icc.mpr ⟨(hS D hD).2.1, (hS D hD).2.2⟩) (infiniteJointMoment L)
  calc
    _ ≤ ∑ I ∈ (Icc 1 r).biUnion target, infiniteJointMoment L I :=
      sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ ↦ infiniteJointMoment_nonneg L I)
    _ ≤ ∑ s ∈ Icc 1 r, ∑ I ∈ target s, infiniteJointMoment L I :=
      GraphStarWeights.sum_biUnion_le_nonneg _ _ _ (infiniteJointMoment_nonneg L)
    _ ≤ ∑ s ∈ Icc 1 r, (r.factorial : ℝ) * (N : ℝ) ^ ε *
        ∑ D ∈ source s, infiniteJointMoment L D := sum_le_sum hcell
    _ = ((r.factorial : ℝ) * (N : ℝ) ^ ε) *
        ∑ s ∈ Icc 1 r, ∑ D ∈ source s, infiniteJointMoment L D := by rw [mul_sum]
    _ = _ := by rw [hsplit]

end PaperP1.VariableSeedMassPropagation
