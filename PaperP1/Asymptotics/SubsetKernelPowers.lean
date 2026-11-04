module

public import PaperP1.Arithmetic.SubsetSingletonBudget
public import PaperP1.Asymptotics.SubsetDefectDensity
public import PaperP1.Asymptotics.SubsetComponentHostCount
public import PaperP1.Asymptotics.CriticalPairKernelPowers

/-! # Binary powers of the two-subset loss use the actual new-set cardinality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetKernelPowers

open Finset PaperP1.Model PaperP1.SubsetEvenLoss PaperP1.SubsetEnvelopeRank
  PaperP1.SubsetTargetComponents PaperP1.SubsetComponentHostData

theorem uniform_global (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℕ, ∀ U V : Finset ℕ,
      V.card ≤ 2 * (L + 1) → (2 ^ loss H U V : ℝ) ≤ (N : ℝ) ^ (2 + ε) := by
  obtain ⟨N₀, hp⟩ := CriticalPairKernelPowers.power_of_rank C 2 0 ε (by norm_num) hε
  refine ⟨N₀, ?_⟩
  intro N hN L hcrit H U V hcard
  have hr : (loss H U V : ℝ) ≤ 2 * ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast (loss_le_card H U V).trans ((Nat.sub_le _ _).trans hcard)
  apply hp N hN L (loss H U V) hcrit
  have hh : 0 ≤ (ε / 2) * ((L + 1 : ℕ) : ℝ) := mul_nonneg (by positivity) (Nat.cast_nonneg _)
  nlinarith only [hr, hh]

theorem few_components (Q : ℕ) (C η ε : ℝ) (Dwidth Dcut : ℕ) (hη : 0 ≤ η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dwidth * (L + 1) →
      2 * R ≤ H → H ≤ Dcut * (L + 1) →
      ∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ y ∈ dyadicBlock N, ∀ U V : Finset ℕ,
      (∀ n ∈ U, |(n : ℤ) - x| ≤ (R : ℤ)) → (∀ n ∈ V, |(n : ℤ) - y| ≤ (R : ℤ)) →
      ((nontrivial x y H R U V).card : ℝ) ≤ η * ((L + 1 : ℕ) : ℝ) →
      (2 ^ loss H U V : ℝ) ≤ (N : ℝ) ^ (η + ε) := by
  obtain ⟨Nd, hd⟩ := SubsetDefectDensity.uniform_density C (ε / 2) Dwidth Dcut (by positivity)
  obtain ⟨Np, hp⟩ := CriticalPairKernelPowers.power_of_rank C η 0 ε hη hε
  obtain ⟨Nw, hw⟩ := EnlargedOffsetRegime.uniform_widths C Dwidth
  refine ⟨max Nd (max Np Nw), ?_⟩
  intro N hN L H R hcrit hR hamb hH x hx y hy U V hU hV hc
  have hRN : R < N := (hw N (by omega) L R hcrit hR).2.2
  have hxR := hRN.trans_le (mem_Ico.mp hx).1
  have hyR := hRN.trans_le (mem_Ico.mp hy).1
  have hr : (loss H U V : ℝ) ≤ (defective y H R V).card + (nontrivial x y H R U V).card := by
    exact_mod_cast loss_le_defects_add_components hxR hyR U V
      (fun n hn ↦ AsymmetricEnvelopeGraph.old_forward hxR hamb (hU n hn))
      (fun n hn ↦ AsymmetricEnvelopeGraph.old_forward hyR hamb (hV n hn))
  have hD := hd N (by omega) L H R hcrit hR hH y hy V hV
  apply hp N (by omega) L (loss H U V) hcrit
  nlinarith only [hr, hD, hc]

theorem few_typed (Q : ℕ) (C ε : ℝ) (Dwidth Dcut : ℕ) (hε : 0 < ε) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ k : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dwidth * (L + 1) →
      2 * R ≤ H → H ≤ Dcut * (L + 1) →
      ∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ y ∈ dyadicBlock N, ∀ U V : Finset ℕ,
      (∀ n ∈ U, |(n : ℤ) - x| ≤ (R : ℤ)) → (∀ n ∈ V, |(n : ℤ) - y| ≤ (R : ℤ)) →
      V.card ≤ 2 * (L + 1) → (∀ a ∈ Icc 1 K, (typed x y H R U V a).card ≤ k) →
      (2 ^ loss H U V : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  let K := ⌈2 * ((2 * Dwidth + 1 : ℕ) : ℝ) / ε⌉₊
  have hK : 1 ≤ K := Nat.ceil_pos.mpr (by positivity)
  have hceil : 2 * ((2 * Dwidth + 1 : ℕ) : ℝ) / ε ≤ (K : ℝ) := Nat.le_ceil _
  have hprod := (div_le_iff₀ hε).mp hceil
  have hratio : ((2 * Dwidth + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) ≤ ε / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((K + 1 : ℕ) : ℝ))).mpr
    push_cast
    push_cast at hprod
    nlinarith only [hprod, hε]
  obtain ⟨Nd, hd⟩ := SubsetDefectDensity.uniform_density C (ε / 2) Dwidth Dcut (by positivity)
  obtain ⟨Nw, hw⟩ := EnlargedOffsetRegime.uniform_widths C Dwidth
  refine ⟨K, hK, ?_⟩
  intro k
  obtain ⟨Np, hp⟩ := CriticalPairKernelPowers.power_of_rank C 1 ((K : ℝ) * k / 2) ε (by norm_num) hε
  refine ⟨max Nd (max Nw Np), ?_⟩
  intro N hN L H R hcrit hR hamb hH x hx y hy U V hU hV hcard ht
  have hRN : R < N := (hw N (by omega) L R hcrit hR).2.2
  have hxR := hRN.trans_le (mem_Ico.mp hx).1
  have hyR := hRN.trans_le (mem_Ico.mp hy).1
  have hnum : ((2 * R + 1 : ℕ) : ℝ) ≤ ((2 * Dwidth + 1 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * R + 1 ≤ (2 * Dwidth + 1) * (L + 1) by nlinarith only [hR])
  have htail : ((2 * R + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ) ≤ (ε / 2) * ((L + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ (((2 * Dwidth + 1 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ)) / ((K + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = (((2 * Dwidth + 1 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ)) * ((L + 1 : ℕ) : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)
  have hs := SubsetSingletonBudget.singleton_budget (H := H) hxR hyR U V hU K k ht
  have hD := hd N (by omega) L H R hcrit hR hH y hy V hV
  have hcardR : (V.card : ℝ) ≤ 2 * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
  have hr : 2 * (loss H U V : ℝ) ≤ (V.card : ℝ) + (singletonCount x y H R U V : ℝ) := by
    exact_mod_cast twice_loss_le_actual_budget hxR hyR U V
      (fun n hn ↦ AsymmetricEnvelopeGraph.old_forward hxR hamb (hU n hn))
      (fun n hn ↦ AsymmetricEnvelopeGraph.old_forward hyR hamb (hV n hn))
  apply hp N (by omega) L (loss H U V) hcrit
  nlinarith only [hs, hD, hr, htail, hcardR]

end PaperP1.SubsetKernelPowers
