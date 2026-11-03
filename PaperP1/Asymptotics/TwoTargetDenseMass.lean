module

public import PaperP1.Asymptotics.TwoTargetNonalignedMass
public import PaperP1.Asymptotics.TwoTargetWeakMass
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # The full nonaligned-or-weak-aligned two-target mass with one uniform positive intersection threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetDenseMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.TwoTargetWindowSections

local instance denseMassPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem uniform_mass (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
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
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
        (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∨
          (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ θ * L) →
        (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧ Disjoint W (squareClassSpace p.2 L) ∧
          η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
        (∑ p ∈ F, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
          (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) ≤ (N : ℝ) ^ (-1 + ε)) := by
  obtain ⟨t₁, Ds₁, k₁, t₂, k₂, ht₁, hDs₁, ht₂, hk₂, hn⟩ :=
    TwoTargetNonalignedMass.uniform_mass s C η (ε / 2) hη (by positivity)
  obtain ⟨θ, hθ, t₃, Ds₂, k₃, t₄, k₄, ht₃, hDs₂, ht₄, hk₄, hw⟩ :=
    TwoTargetWeakMass.uniform_mass s C η (ε / 2) hη (by positivity)
  obtain ⟨Na, ha⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨θ, hθ, t₁, Ds₁, k₁, t₂, k₂, t₃, Ds₂, k₃, t₄, k₄,
    ht₁, hDs₁, ht₂, hk₂, ht₃, hDs₂, ht₄, hk₄, ?_⟩
  intro hCL₁ hCU₁ hPL₁ hPU₁ hCL₂ hCU₂ hPL₂ hPU₂
  obtain ⟨Nn, _hNn, hn⟩ := hn hCL₁ hCU₁ hPL₁ hPU₁
  obtain ⟨Nw, _hNw, hw⟩ := hw hCL₂ hCU₂ hPL₂ hPU₂
  refine ⟨max 3 (max Na (max Nn Nw)), by omega, ?_⟩
  intro N hN L hband x hx W hW F hdyadic hadmiss hdense
  classical
  let nonaligned := F.filter fun p ↦ ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L
  let aligned := F \ nonaligned
  have hnF : nonaligned ⊆ F := filter_subset _ _
  have hwF : aligned ⊆ F := sdiff_subset
  have hncount := hn N (by omega) L hband x hx W hW nonaligned
    (fun p hp ↦ hdyadic p (hnF hp)) (fun _ hp ↦ (mem_filter.mp hp).2)
    (fun p hp ↦ hdense p (hnF hp))
  have hwcount := hw N (by omega) L hband x hx W hW aligned
    (fun p hp ↦ hdyadic p (hwF hp)) (by
      intro p hp
      obtain ⟨hpF, hpnot⟩ := mem_sdiff.mp hp
      have haligned : CompressedTargetAlignment.Aligned 1 p.1 p.2 L := by
        by_contra h
        exact hpnot (mem_filter.mpr ⟨hpF, h⟩)
      exact ⟨haligned, (hadmiss p hpF).resolve_left (fun h ↦ h haligned)⟩)
    (fun p hp ↦ hdense p (hwF hp))
  have hpart := sum_sdiff (f := fun p : ℕ × ℕ ↦ infiniteMarginal p.1 L * infiniteMarginal p.2 L *
    (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) hnF
  change (∑ p ∈ aligned, _) + (∑ p ∈ nonaligned, _) = _ at hpart
  have hsum : (∑ p ∈ F, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
      (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) ≤ 2 * (N : ℝ) ^ (-1 + ε / 2) := by
    linarith only [hpart, hncount, hwcount]
  calc
    _ ≤ 2 * (N : ℝ) ^ (-1 + ε / 2) := hsum
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.TwoTargetDenseMass
