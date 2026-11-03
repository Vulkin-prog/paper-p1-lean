module

public import PaperP1.Asymptotics.TwoTargetNonalignedMass
public import PaperP1.Arithmetic.TwoTargetDensePairs

/-! # The literal nonaligned summand of article Lemma15.2, with source exclusion and the printed deficit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetNonalignedMassTheorem

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetDensePairs

local instance nonalignedMassTheoremPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem article_15_2_nonaligned (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ t₁ Ds k₁ t₂ k₂ : ℕ, 2 ≤ t₁ ∧ 0 < Ds ∧ 2 ≤ t₂ ∧ 1 ≤ k₂ ∧
      (UniformSourceSurfaceCover.UniformCover k₁ (t₁ - 1) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₂ (t₂ - 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k₁) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
        (∑ p ∈ pairs x W N L η, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
          (2 ^ deficit W p.1 p.2 L : ℝ)) ≤ (N : ℝ) ^ (-1 + ε)) := by
  obtain ⟨t₁, Ds, k₁, t₂, k₂, ht₁, hDs, ht₂, hk₂, hm⟩ :=
    TwoTargetNonalignedMass.uniform_mass s C η ε hη hε
  refine ⟨t₁, Ds, k₁, t₂, k₂, ht₁, hDs, ht₂, hk₂, ?_⟩
  intro hCoverL hCoverU hPilaL hPilaU
  obtain ⟨N₀, hN₀, hu⟩ := hm hCoverL hCoverU hPilaL hPilaU
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband x hx W hW
  have hmass := hu N hN L hband x hx W hW (pairs x W N L η) (by
    intro p hp
    have h := (mem_pairs x W N L η p).mp hp
    exact ⟨h.1, h.2.1⟩) (by
    intro p hp
    exact ((mem_pairs x W N L η p).mp hp).2.2.2.2.1) (by
    intro p hp
    have h := ((mem_pairs x W N L η p).mp hp).2.2.2.2.2
    refine ⟨h.1, h.2.1, ?_⟩
    rw [← deficit_eq_kernel x L W hW p.1 p.2]
    exact h.2.2)
  simpa only [deficit_eq_kernel x L W hW] using hmass

end PaperP1.TwoTargetNonalignedMassTheorem
