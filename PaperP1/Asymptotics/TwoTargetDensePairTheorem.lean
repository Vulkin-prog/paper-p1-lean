module

public import PaperP1.Asymptotics.TwoTargetDenseMass
public import PaperP1.Arithmetic.TwoTargetAdmissibleDensePairs

/-! # The complete first conclusion of article Lemma15.2, including weak alignment, source exclusion and the printed deficit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetDensePairTheorem

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetDensePairs PaperP1.TwoTargetAdmissibleDensePairs

local instance densePairTheoremPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem article_15_2_dense_pair (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ t₁ Ds₁ k₁ t₂ k₂ t₃ Ds₂ k₃ t₄ k₄ : ℕ,
      2 ≤ t₁ ∧ 0 < Ds₁ ∧ 2 ≤ t₂ ∧ 1 ≤ k₂ ∧ 2 ≤ t₃ ∧ 0 < Ds₂ ∧ 2 ≤ t₄ ∧ 1 ≤ k₄ ∧
      (UniformSourceSurfaceCover.UniformCover k₁ (t₁ - 1) Ds₁ →
      UniformOrdinarySurfaceCover.UniformCover k₂ (t₂ - 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds₁ + 2).choose 2 + k₁) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      UniformSourceSurfaceCover.UniformCover k₃ (t₃ - 1) Ds₂ →
      UniformOrdinarySurfaceCover.UniformCover k₄ (t₄ - 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds₂ + 2).choose 2 + k₃) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₄ + 3) M) →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
        (∑ p ∈ TwoTargetAdmissibleDensePairs.pairs x W N L η θ,
          infiniteMarginal p.1 L * infiniteMarginal p.2 L * (2 ^ deficit W p.1 p.2 L : ℝ)) ≤
          (N : ℝ) ^ (-1 + ε)) := by
  obtain ⟨θ, hθ, t₁, Ds₁, k₁, t₂, k₂, t₃, Ds₂, k₃, t₄, k₄,
      ht₁, hDs₁, ht₂, hk₂, ht₃, hDs₂, ht₄, hk₄, hm⟩ :=
    TwoTargetDenseMass.uniform_mass s C η ε hη hε
  refine ⟨θ, hθ, t₁, Ds₁, k₁, t₂, k₂, t₃, Ds₂, k₃, t₄, k₄,
    ht₁, hDs₁, ht₂, hk₂, ht₃, hDs₂, ht₄, hk₄, ?_⟩
  intro hCL₁ hCU₁ hPL₁ hPU₁ hCL₂ hCU₂ hPL₂ hPU₂
  obtain ⟨N₀, hN₀, hu⟩ := hm hCL₁ hCU₁ hPL₁ hPU₁ hCL₂ hCU₂ hPL₂ hPU₂
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband x hx W hW
  have hmass := hu N hN L hband x hx W hW (TwoTargetAdmissibleDensePairs.pairs x W N L η θ) (by
    intro p hp
    have h := (TwoTargetAdmissibleDensePairs.mem_pairs x W N L η θ p).mp hp
    exact ⟨h.1, h.2.1⟩) (by
    intro p hp
    exact ((TwoTargetAdmissibleDensePairs.mem_pairs x W N L η θ p).mp hp).2.2.2.2.1) (by
    intro p hp
    have h := ((TwoTargetAdmissibleDensePairs.mem_pairs x W N L η θ p).mp hp).2.2.2.2.2
    refine ⟨h.1, h.2.1, ?_⟩
    rw [← deficit_eq_kernel x L W hW p.1 p.2]
    exact h.2.2)
  simpa only [deficit_eq_kernel x L W hW] using hmass

end PaperP1.TwoTargetDensePairTheorem
