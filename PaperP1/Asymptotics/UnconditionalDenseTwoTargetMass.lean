module

public import PaperP1.Asymptotics.DenseTwoTargetNonalignedHosts
public import PaperP1.Asymptotics.DenseTwoTargetWeakHosts
public import PaperP1.Asymptotics.HomogeneousLocalMarginalCap
public import PaperP1.Asymptotics.ActualPairRowActivity
public import PaperP1.Asymptotics.CriticalChannelPowers

/-! # Full actual, homogeneous and nominal dense target weights above arbitrary source subspaces

The full effective source subspace is allowed; local defects and zero actual
marginals are retained. No source/target pair-disjointness beyond W is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnconditionalDenseTwoTargetMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.TwoTargetWindowSections

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem uniform_hosts (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∨
        (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ (η / 64) * L) →
      (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧ Disjoint W (squareClassSpace p.2 L) ∧
        η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  classical
  obtain ⟨NN, _hNN, hn⟩ := DenseTwoTargetNonalignedHosts.uniform_hosts s C η (ε / 2) hη (by positivity)
  obtain ⟨NW, _hNW, hw⟩ := DenseTwoTargetWeakHosts.uniform_hosts s C η (ε / 2) hη (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 2 (ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NN + NW + NA, by omega, ?_⟩
  intro N hN L hband x hx W hW F hdyadic hadmiss hdense
  let FN := F.filter fun p ↦ ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L
  let FW := F \ FN
  have hFN : FN ⊆ F := filter_subset _ _
  have hFW : FW ⊆ F := sdiff_subset
  have hnF := hn N (by omega) L hband x hx W hW FN
    (fun p hp ↦ hdyadic p (hFN hp)) (fun _ hp ↦ (mem_filter.mp hp).2)
    (fun p hp ↦ hdense p (hFN hp))
  have hwF := hw N (by omega) L hband x hx W hW FW
    (fun p hp ↦ hdyadic p (hFW hp)) (by
      intro p hp
      obtain ⟨hpF, hpnot⟩ := mem_sdiff.mp hp
      have haligned : CompressedTargetAlignment.Aligned 1 p.1 p.2 L := by
        by_contra hh
        exact hpnot (mem_filter.mpr ⟨hpF, hh⟩)
      exact ⟨haligned, (hadmiss p hpF).resolve_left (fun hh ↦ hh haligned)⟩)
    (fun p hp ↦ hdense p (hFW hp))
  have hpart : (FW.card : ℝ) + FN.card = F.card := by
    exact_mod_cast card_sdiff_add_card_eq_card hFN
  calc
    _ ≤ 2 * (N : ℝ) ^ (ε / 2) := by linarith only [hpart, hnF, hwF]
    _ ≤ (N : ℝ) ^ (ε / 2 + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_mass (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∨
        (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ (η / 64) * L) →
      (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧
        Disjoint W (squareClassSpace p.2 L) ∧
        η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
      (∑ p ∈ F, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NH, _hNH, hh⟩ := uniform_hosts s C η (ε / 2) hη (by positivity)
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
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∨
        (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ (η / 64) * L) →
      (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧
        Disjoint W (squareClassSpace p.2 L) ∧
        η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
      (∑ p ∈ F, ((2 ^ L : ℝ)⁻¹) ^ 2 *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NH, _hNH, hh⟩ := uniform_hosts s C η (ε / 2) hη (by positivity)
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


theorem uniform_homogeneous_mass (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∨
        (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ (η / 64) * L) →
      (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧
        Disjoint W (squareClassSpace p.2 L) ∧
        η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
      (∑ p ∈ F, HomogeneousRunMass.probability L {p.1} * HomogeneousRunMass.probability L {p.2} *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NH, _hNH, hh⟩ := uniform_hosts s C η (ε / 2) hη (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := HomogeneousLocalMarginalCap.uniform_cap C
  let M := 2 * (2 : ℝ) ^ C
  let K := M ^ 2 * (2 : ℝ) ^ C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption K (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NH + NM + NA, by omega, ?_⟩
  intro N hN L hband x hx W hW F hdyadic hnon hdense
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard := hh N (by omega) L hband x hx W hW F hdyadic hnon hdense
  have hpoint (p : ℕ × ℕ) (hp : p ∈ F) :
      HomogeneousRunMass.probability L {p.1} * HomogeneousRunMass.probability L {p.2} *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ) ≤ K / N := by
    have hy := hm N (by omega) L hband p.1 (hdyadic p hp).1
    have hz := hm N (by omega) L hband p.2 (hdyadic p hp).2
    have hprod : HomogeneousRunMass.probability L {p.1} * HomogeneousRunMass.probability L {p.2} ≤ (M / N) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hy hz
        ((HomogeneousRunMass.probability_pos L {p.2}).le) (by positivity : 0 ≤ M / N)
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


theorem article_15_2 (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∨
        (Module.finrank F₂ ↥(squareClassSpace p.1 L ⊓ squareClassSpace p.2 L) : ℝ) ≤ θ * L) →
      (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧
        Disjoint W (squareClassSpace p.2 L) ∧
        η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
      (∑ p ∈ F, infiniteMarginal p.1 L * infiniteMarginal p.2 L *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) ≤
        (N : ℝ) ^ (-1 + ε) ∧
      (∑ p ∈ F, HomogeneousRunMass.probability L {p.1} * HomogeneousRunMass.probability L {p.2} *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) ≤ (N : ℝ) ^ (-1 + ε) ∧
      (∑ p ∈ F, ((2 ^ L : ℝ)⁻¹) ^ 2 *
        (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NA, _hNA, ha⟩ := uniform_mass s C η ε hη hε
  obtain ⟨NH, _hNH, hh⟩ := uniform_homogeneous_mass s C η ε hη hε
  obtain ⟨NN, _hNN, hn⟩ := uniform_nominal_mass s C η ε hη hε
  refine ⟨η / 64, by positivity, 3 + NA + NH + NN, by omega, ?_⟩
  intro N hN L hband x hx W hW F hdyadic hadmiss hdense
  exact ⟨ha N (by omega) L hband x hx W hW F hdyadic hadmiss hdense,
    hh N (by omega) L hband x hx W hW F hdyadic hadmiss hdense,
    hn N (by omega) L hband x hx W hW F hdyadic hadmiss hdense⟩


end PaperP1.UnconditionalDenseTwoTargetMass
