module

public import PaperP1.Asymptotics.TwoTargetNonalignedRankWeight
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # The literal nonaligned dense two-target mass uses exact heterogeneous marginals and the effective rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetNonalignedMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.TwoTargetWindowSections

local instance nonalignedMassPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem uniform_mass (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ t₁ Ds k₁ t₂ k₂ : ℕ, 2 ≤ t₁ ∧ 0 < Ds ∧ 2 ≤ t₂ ∧ 1 ≤ k₂ ∧
      (UniformSourceSurfaceCover.UniformCover k₁ (t₁ - 1) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₂ (t₂ - 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k₁) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
        (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
        (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧ Disjoint W (squareClassSpace p.2 L) ∧
          η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
        (∑ p ∈ F, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
          (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) ≤ (N : ℝ) ^ (-1 + ε)) := by
  obtain ⟨t₁, Ds, k₁, t₂, k₂, ht₁, hDs, ht₂, hk₂, hweight⟩ :=
    TwoTargetNonalignedRankWeight.uniform_weight s C η (ε / 2) hη (by positivity)
  obtain ⟨Nm, _hNm, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  let M := 2 * (2 : ℝ) ^ C
  refine ⟨t₁, Ds, k₁, t₂, k₂, ht₁, hDs, ht₂, hk₂, ?_⟩
  intro hCoverL hCoverU hPilaL hPilaU
  obtain ⟨A, _hA, Nw, _hNw, hw⟩ := hweight hCoverL hCoverU hPilaL hPilaU
  obtain ⟨Na, ha⟩ := HalfCountSchedule.factor_absorption (M ^ 2 * A) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 3 (max Nm (max Nw Na)), by omega, ?_⟩
  intro N hN L hband x hx W hW F hdyadic hnon hdense
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount := hw N (by omega) L hband x hx W hW F hdyadic hnon hdense
  have hprod (p : ℕ × ℕ) (hp : p ∈ F) : infiniteMarginal p.1 L * infiniteMarginal p.2 L ≤ (M / N) ^ 2 := by
    have hp1 := hm N (by omega) L hband p.1 (hdyadic p hp).1
    have hp2 := hm N (by omega) L hband p.2 (hdyadic p hp).2
    have hp10 := MissingBlockProbabilities.infiniteMarginal_nonneg p.1 L
    have hp20 := MissingBlockProbabilities.infiniteMarginal_nonneg p.2 L
    have hcap : 0 ≤ M / N := hp10.trans hp1
    simpa only [pow_two] using mul_le_mul hp1 hp2 hp20 hcap
  have hfinite : (∑ p ∈ F, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
      (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) ≤
      (M / N) ^ 2 * ∑ p ∈ F, (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ) := by
    have h := sum_le_sum (fun p hp ↦ mul_le_mul_of_nonneg_right (hprod p hp)
      (by positivity : (0 : ℝ) ≤ 2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W)))
    rw [← mul_sum] at h
    exact h
  calc
    _ ≤ (M / N) ^ 2 * (A * (N : ℝ) ^ (1 + ε / 2)) :=
      hfinite.trans (mul_le_mul_of_nonneg_left hcount (sq_nonneg _))
    _ = (M ^ 2 * A) * (N : ℝ) ^ (-1 + ε / 2) := by
      have hneg : ((N : ℝ) ^ 2)⁻¹ = (N : ℝ) ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hNr.le, Real.rpow_two]
      rw [div_pow, div_eq_mul_inv, hneg]
      calc
        _ = (M ^ 2 * A) * ((N : ℝ) ^ (-2 : ℝ) * (N : ℝ) ^ (1 + ε / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hNr]; congr 2; ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.TwoTargetNonalignedMass
