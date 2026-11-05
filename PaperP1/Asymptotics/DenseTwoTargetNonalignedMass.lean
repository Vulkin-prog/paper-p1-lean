module

public import PaperP1.Asymptotics.DenseTwoTargetNonalignedHosts
public import PaperP1.Asymptotics.ActualPairRowActivity
public import PaperP1.Asymptotics.CriticalChannelPowers

/-! # Actual and nominal dense nonaligned target weights above arbitrary source subspaces

The full effective source subspace is allowed; local defects and zero actual
marginals are retained. No source/target pair-disjointness beyond W is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseTwoTargetNonalignedMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.TwoTargetWindowSections

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem uniform_mass (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
      (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧
        Disjoint W (squareClassSpace p.2 L) ∧
        η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
      (∑ p ∈ F, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NH, _hNH, hh⟩ := DenseTwoTargetNonalignedHosts.uniform_hosts s C η (ε / 2) hη (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  let M := 2 * (2 : ℝ) ^ C
  let K := M ^ 2 * (2 : ℝ) ^ C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption K (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NH + NM + NA, by omega, ?_⟩
  intro N hN L hband x hx W hW F hdyadic hnon hdense
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard := hh N (by omega) L hband x hx W hW F hdyadic hnon hdense
  have hpoint (p : ℕ × ℕ) (hp : p ∈ F) :
      infiniteMarginal p.1 L * infiniteMarginal p.2 L *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ) ≤ K / N := by
    have hy := hm N (by omega) L hband p.1 (hdyadic p hp).1
    have hz := hm N (by omega) L hband p.2 (hdyadic p hp).2
    have hprod : infiniteMarginal p.1 L * infiniteMarginal p.2 L ≤ (M / N) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hy hz
        (MissingBlockProbabilities.infiniteMarginal_nonneg p.2 L) (by positivity : 0 ≤ M / N)
    have hdim := dimension_le_length p.1 p.2 L W (hdense p hp).2.1
    have hpow := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdim).trans
      (CriticalChannelPowers.word_upper (by omega : 2 ≤ N) hband)
    calc
      _ ≤ (M / N) ^ 2 * ((2 : ℝ) ^ C * N) := mul_le_mul hprod hpow (by positivity) (by positivity)
      _ = _ := by dsimp [K]; field_simp
  calc
    _ ≤ ∑ _p ∈ F, K / N := sum_le_sum hpoint
    _ = (F.card : ℝ) * (K / N) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (K / N) := mul_le_mul_of_nonneg_right hcard (by dsimp [K]; positivity)
    _ = K * (N : ℝ) ^ (-1 + ε / 2) := by
      rw [show -1 + ε / 2 = ε / 2 - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
      ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring


theorem uniform_nominal_mass (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
      (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧
        Disjoint W (squareClassSpace p.2 L) ∧
        η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
      (∑ p ∈ F, ((2 ^ L : ℝ)⁻¹) ^ 2 *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NH, _hNH, hh⟩ := DenseTwoTargetNonalignedHosts.uniform_hosts s C η (ε / 2) hη (by positivity)
  let K := ((2 : ℝ) ^ C) ^ 3
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption K (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NH + NA, by omega, ?_⟩
  intro N hN L hband x hx W hW F hdyadic hnon hdense
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard := hh N (by omega) L hband x hx W hW F hdyadic hnon hdense
  have hpoint (p : ℕ × ℕ) (hp : p ∈ F) :
      ((2 ^ L : ℝ)⁻¹) ^ 2 *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ) ≤ K / N := by
    have hnom := LocalRigidityConsequences.nominal_marginal_bound (by omega : 2 ≤ N) hband
    have hdim := dimension_le_length p.1 p.2 L W (hdense p hp).2.1
    have hpow := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdim).trans
      (CriticalChannelPowers.word_upper (by omega : 2 ≤ N) hband)
    calc
      _ ≤ ((2 : ℝ) ^ C / N) ^ 2 * ((2 : ℝ) ^ C * N) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hnom 2) hpow (by positivity) (by positivity)
      _ = _ := by dsimp [K]; field_simp
  calc
    _ ≤ ∑ _p ∈ F, K / N := sum_le_sum hpoint
    _ = (F.card : ℝ) * (K / N) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (K / N) := mul_le_mul_of_nonneg_right hcard (by dsimp [K]; positivity)
    _ = K * (N : ℝ) ^ (-1 + ε / 2) := by
      rw [show -1 + ε / 2 = ε / 2 - 1 by ring, Real.rpow_sub hn, Real.rpow_one]
      ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring


end PaperP1.DenseTwoTargetNonalignedMass
