module

public import PaperP1.Asymptotics.ExpandedAsymmetricKernelPowers
public import PaperP1.Asymptotics.EnlargedOffsetRegime
public import PaperP1.Asymptotics.AsymmetricSubsetComponents
public import PaperP1.Asymptotics.SubsetDenseNonalignedHosts

/-! # The actual asymmetric dense weighted sector with internal pinned-support confinement -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExpandedAsymmetricDenseMass

open Finset PaperP1.Model PaperP1.AsymmetricEvenLoss PaperP1.AsymmetricComponentHostData

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_weight (Q : ℕ) (hQ : 1 ≤ Q) (C ε η : ℝ) (Dold Dcut : ℕ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H R : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dold * (L + 1) →
      ∀ (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H), H ≤ Dcut * (L + 1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ ExpandedAsymmetricSupportEnvelope.block N Q ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned Dold p.1 p.2 L) →
      (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ (nontrivial p.1 p.2 L H R hnew hamb (old p.1)).card) →
      (∑ p ∈ F, (2 ^ loss H (old p.1) p.2 L : ℝ)) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨ND, _hND, hd⟩ := SubsetDenseNonalignedHosts.uniform_dense Q hQ C (ε / 2) η
    Dold Dcut (by positivity) hη
  obtain ⟨NP, hp⟩ := AsymmetricKernelPowers.uniform_global C (ε / 2) (by positivity)
  obtain ⟨NW, hw⟩ := EnlargedOffsetRegime.uniform_widths C Dold
  refine ⟨3 + ND + NP + NW, by omega, ?_⟩
  intro N hN L H R hcrit hR hnew hamb hH old hold F hF hnon hdense
  have hRN : R < N := (hw N (by omega) L R hcrit hR).2.2
  have hnewWidth : ∀ y ∈ dyadicBlock N, ∀ n ∈ NormalizedWindowSets.values y L,
      |(n : ℤ) - y| ≤ (R : ℤ) := by
    intro y hy n hn
    have hyp : 0 < y := by have hh := (mem_Ico.mp hy).1; omega
    obtain ⟨i, rfl⟩ := NormalizedWindowSets.mem_values.mp hn
    rw [NormalizedUnitCount.label_cast hyp, add_sub_cancel_left]
    exact (EnlargedPairGeometry.offset_abs i).trans (by exact_mod_cast hnew)
  have hcount : (F.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    apply hd N (by omega) L H R hcrit hR (by omega) hH old
      (fun y ↦ NormalizedWindowSets.values y L) hold hnewWidth F hF hnon
    intro p hpF
    have hyR : R < p.2 := hRN.trans_le (mem_Ico.mp (hF p hpF).2).1
    have hc : ((AsymmetricComponentHostData.nontrivial p.1 p.2 L H R hnew hamb (old p.1)).card : ℝ) ≤
        (SubsetComponentHostData.nontrivial p.1 p.2 H R (old p.1) (NormalizedWindowSets.values p.2 L)).card := by
      exact_mod_cast card_le_card (AsymmetricSubsetComponents.nontrivial_subset hyR hnew hamb (old p.1))
    exact (hdense p hpF).trans hc
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ∑ _p ∈ F, (N : ℝ) ^ (1 + ε / 2) :=
      sum_le_sum (fun p _hp ↦ hp N (by omega) L hcrit H p.2 (old p.1))
    _ = (F.card : ℝ) * (N : ℝ) ^ (1 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 + ε / 2) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.ExpandedAsymmetricDenseMass
