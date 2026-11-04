module

public import PaperP1.Asymptotics.AsymmetricKernelPowers
public import PaperP1.Asymptotics.ExpandedAsymmetricDefectDensity

/-! # Original-length asymmetric powers on expanded comparable ranges -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExpandedAsymmetricKernelPowers

open Finset PaperP1.AsymmetricEvenLoss PaperP1.AsymmetricEnvelopeRank
  PaperP1.AsymmetricTargetComponents PaperP1.AsymmetricComponentHostData

theorem few_components (Q : ℕ) (C η ε : ℝ) (Dold Dcut : ℕ) (hη : 0 ≤ η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dold * (L + 1) →
      ∀ (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H), H ≤ Dcut * (L + 1) →
      ∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ y ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ old : Finset ℕ,
      (∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ)) →
      ((nontrivial x y L H R hnew hamb old).card : ℝ) ≤ η * ((L + 1 : ℕ) : ℝ) →
      (2 ^ loss H old y L : ℝ) ≤ (N : ℝ) ^ (η + ε) := by
  obtain ⟨Nd, hd⟩ := ExpandedAsymmetricDefectDensity.uniform_density Q C (ε / 2) Dcut (by positivity)
  obtain ⟨Np, hp⟩ := CriticalPairKernelPowers.power_of_rank C η 0 ε hη hε
  obtain ⟨Nw, hw⟩ := EnlargedOffsetRegime.uniform_widths C Dold
  refine ⟨max Nd (max Np Nw), ?_⟩
  intro N hN L H R hcrit hR hnew hamb hH x hx y hy old hold hc
  have hRN : R < N := (hw N (by omega) L R hcrit hR).2.2
  have hxR := hRN.trans_le (mem_Ico.mp hx).1
  have hyR := hRN.trans_le (mem_Ico.mp hy).1
  have hr : (loss H old y L : ℝ) ≤ (defective y L H).card + (nontrivial x y L H R hnew hamb old).card := by
    exact_mod_cast loss_le_defects_add_components hxR hyR hnew hamb old hold
  have hD := hd N (by omega) L H hcrit hH y hy
  apply hp N (by omega) L (loss H old y L) hcrit
  nlinarith only [hr, hD, hc]

theorem few_typed (Q : ℕ) (C ε : ℝ) (Dold Dcut : ℕ) (hε : 0 < ε) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ k : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dold * (L + 1) →
      ∀ (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H), H ≤ Dcut * (L + 1) →
      ∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ y ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ old : Finset ℕ,
      (∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ)) →
      (∀ a ∈ Icc 1 K, (typed x y L H R hnew hamb old a).card ≤ k) →
      (2 ^ loss H old y L : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  let K := ⌈2 * ((2 * Dold + 1 : ℕ) : ℝ) / ε⌉₊
  have hK : 1 ≤ K := Nat.ceil_pos.mpr (by positivity)
  have hceil : 2 * ((2 * Dold + 1 : ℕ) : ℝ) / ε ≤ (K : ℝ) := Nat.le_ceil _
  have hprod := (div_le_iff₀ hε).mp hceil
  have hratio : ((2 * Dold + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) ≤ ε / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((K + 1 : ℕ) : ℝ))).mpr
    push_cast
    push_cast at hprod
    nlinarith only [hprod, hε]
  obtain ⟨Nd, hd⟩ := ExpandedAsymmetricDefectDensity.uniform_density Q C (ε / 2) Dcut (by positivity)
  obtain ⟨Nw, hw⟩ := EnlargedOffsetRegime.uniform_widths C Dold
  refine ⟨K, hK, ?_⟩
  intro k
  obtain ⟨Np, hp⟩ := CriticalPairKernelPowers.power_of_rank C (1 / 2) ((K : ℝ) * k / 2) ε (by norm_num) hε
  refine ⟨max Nd (max Nw Np), ?_⟩
  intro N hN L H R hcrit hR hnew hamb hH x hx y hy old hold ht
  have hRN : R < N := (hw N (by omega) L R hcrit hR).2.2
  have hxR := hRN.trans_le (mem_Ico.mp hx).1
  have hyR := hRN.trans_le (mem_Ico.mp hy).1
  have hnum : ((2 * R + 1 : ℕ) : ℝ) ≤ ((2 * Dold + 1 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * R + 1 ≤ (2 * Dold + 1) * (L + 1) by nlinarith only [hR])
  have htail : ((2 * R + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) ≤ (ε / 2) * ((L + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ (((2 * Dold + 1 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ)) / ((K + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = (((2 * Dold + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ)) * ((L + 1 : ℕ) : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)
  have hs := AsymmetricSingletonBudget.singleton_budget hxR hyR hnew hamb old hold K k ht
  have hD := hd N (by omega) L H hcrit hH y hy
  have hr : 2 * (loss H old y L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) + (singletonCount x y L H R hnew hamb old : ℝ) := by
    exact_mod_cast twice_loss_le_target_budget hxR hyR hnew hamb old hold
  apply hp N (by omega) L (loss H old y L) hcrit
  nlinarith only [hs, hD, hr, htail]

end PaperP1.ExpandedAsymmetricKernelPowers
