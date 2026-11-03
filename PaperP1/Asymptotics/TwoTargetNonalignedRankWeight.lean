module

public import PaperP1.Asymptotics.TwoTargetNonalignedUpperCount
public import PaperP1.Asymptotics.DenseWeightedSectorUnderInputs

/-! # The two actual nonaligned cardinality strata pay the complete effective rank weight -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetNonalignedRankWeight

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.TwoTargetWindowSections

local instance nonalignedRankWeightPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem uniform_weight (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ t₁ Ds k₁ t₂ k₂ : ℕ, 2 ≤ t₁ ∧ 0 < Ds ∧ 2 ≤ t₂ ∧ 1 ≤ k₂ ∧
      (UniformSourceSurfaceCover.UniformCover k₁ (t₁ - 1) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₂ (t₂ - 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k₁) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
        (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
        (∀ p ∈ F, Disjoint W (squareClassSpace p.1 L) ∧ Disjoint W (squareClassSpace p.2 L) ∧
          η * L ≤ (Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) →
        (∑ p ∈ F, (2 ^ Module.finrank F₂ (Kernel p.1 p.2 L W) : ℝ)) ≤ A * (N : ℝ) ^ (1 + ε)) := by
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨t₁, Ds, k₁, ht₁, hDs, hlower⟩ := TwoTargetNonalignedDenseCount.uniform_pairs s C η δ hη hδ
  obtain ⟨t₂, k₂, ht₂, hk₂, hupper⟩ := TwoTargetNonalignedUpperCount.uniform_pairs s C δ δ hδ hδ
  obtain ⟨Nl, hlowpower⟩ := CriticalPairKernelPowers.power_of_rank C (1 / 2) 0 (2 * δ) (by norm_num) (by positivity)
  obtain ⟨Nu, huppower⟩ := CriticalPairKernelPowers.power_of_rank C 1 0 δ (by norm_num) hδ
  refine ⟨t₁, Ds, k₁, t₂, k₂, ht₁, hDs, ht₂, hk₂, ?_⟩
  intro hCoverL hCoverU hPilaL hPilaU
  obtain ⟨Al, hAl, NL, _hNL, hl⟩ := hlower hCoverL hPilaL
  obtain ⟨Au, hAu, NU, _hNU, hu⟩ := hupper hCoverU hPilaU
  refine ⟨Al + Au, by positivity, max 3 (max NL (max NU (max Nl Nu))), by omega, ?_⟩
  intro N hN L hband x hx W hW F hdyadic hnon hdense
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let d := fun p : ℕ × ℕ ↦ Module.finrank F₂ (Kernel p.1 p.2 L W)
  let lowHosts := F.filter fun p ↦ (d p : ℝ) ≤ (1 / 2 + δ) * L
  let highHosts := F \ lowHosts
  have hlowF : lowHosts ⊆ F := filter_subset _ _
  have hhighF : highHosts ⊆ F := sdiff_subset
  have hlowcount := hl N (by omega) L hband x hx W hW lowHosts
    (fun p hp ↦ hdyadic p (hlowF hp)) (fun p hp ↦ hnon p (hlowF hp)) (fun p hp ↦ hdense p (hlowF hp))
  have hhighcount := hu N (by omega) L hband x hx W hW highHosts
    (fun p hp ↦ hdyadic p (hhighF hp)) (fun p hp ↦ hnon p (hhighF hp)) (by
      intro p hp
      obtain ⟨hpF, hpnot⟩ := mem_sdiff.mp hp
      have hnot : ¬ (d p : ℝ) ≤ (1 / 2 + δ) * L := fun h ↦ hpnot (mem_filter.mpr ⟨hpF, h⟩)
      exact ⟨(hdense p hpF).1, (hdense p hpF).2.1, (lt_of_not_ge hnot).le⟩)
  have hlowweight : ∀ p ∈ lowHosts, (2 ^ d p : ℝ) ≤ (N : ℝ) ^ (1 / 2 + 2 * δ) := by
    intro p hp
    apply hlowpower N (by omega) L (d p) hband
    calc
      (d p : ℝ) ≤ (1 / 2 + δ) * L := (mem_filter.mp hp).2
      _ ≤ (1 / 2 + δ) * ((L + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ L) (by positivity)
      _ = _ := by ring
  have hhighweight : ∀ p ∈ highHosts, (2 ^ d p : ℝ) ≤ (N : ℝ) ^ (1 + δ) := by
    intro p hp
    apply huppower N (by omega) L (d p) hband
    have hdim : (d p : ℝ) ≤ L := by
      exact_mod_cast dimension_le_length p.1 p.2 L W (hdense p (hhighF hp)).2.1
    calc
      (d p : ℝ) ≤ (L : ℝ) := hdim
      _ ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ L
      _ = 1 * ((L + 1 : ℕ) : ℝ) := (one_mul _).symm
      _ ≤ (1 + δ / 2) * ((L + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hδ]) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hsumL := DenseWeightedSectorUnderInputs.weighted_card_bound lowHosts (fun p ↦ (2 ^ d p : ℝ))
    (N : ℝ) Al (1 / 2 + δ) (1 / 2 + 2 * δ) hNr hlowcount hlowweight
  have hsumU := DenseWeightedSectorUnderInputs.weighted_card_bound highHosts (fun p ↦ (2 ^ d p : ℝ))
    (N : ℝ) Au δ (1 + δ) hNr hhighcount hhighweight
  have hsumL' : (∑ p ∈ lowHosts, (2 ^ d p : ℝ)) ≤ Al * (N : ℝ) ^ (1 + ε) :=
    hsumL.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1
      (by dsimp [δ]; linarith only [hε])) hAl.le)
  have hsumU' : (∑ p ∈ highHosts, (2 ^ d p : ℝ)) ≤ Au * (N : ℝ) ^ (1 + ε) :=
    hsumU.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1
      (by dsimp [δ]; linarith only [hε])) hAu.le)
  have hpart := sum_sdiff (f := fun p : ℕ × ℕ ↦ (2 ^ d p : ℝ)) hlowF
  change (∑ p ∈ highHosts, (2 ^ d p : ℝ)) + (∑ p ∈ lowHosts, (2 ^ d p : ℝ)) = _ at hpart
  change (∑ p ∈ F, (2 ^ d p : ℝ)) ≤ _
  linarith only [hpart, hsumL', hsumU']

end PaperP1.TwoTargetNonalignedRankWeight
