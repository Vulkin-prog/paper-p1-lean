module

public import PaperP1.Asymptotics.AsymmetricKernelPowers
public import PaperP1.Asymptotics.DenseWeightedSectorUnderInputs

/-! # The actual asymmetric dense weighted sector under the existing geometric properties -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricDenseMassUnderInputs

open Finset PaperP1.Model PaperP1.AsymmetricEvenLoss PaperP1.AsymmetricComponentHostData

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_weight (C ε η : ℝ) (Dold Dcut : ℕ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ Ds kg ko K : ℕ, 0 < Ds ∧ 1 ≤ K ∧
      (UniformSourceSurfaceCover.UniformCover kg (AsymmetricComponentHostCount.sizeCap Dcut η) Ds →
      UniformOrdinarySurfaceCover.UniformCover ko (K + 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + kg) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (ko + 3) M) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H R : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dold * (L + 1) →
      ∀ (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H), H ≤ Dcut * (L + 1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ dyadicBlock N, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned Dold p.1 p.2 L) →
      (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ (nontrivial p.1 p.2 L H R hnew hamb (old p.1)).card) →
      (∑ p ∈ F, (2 ^ loss H (old p.1) p.2 L : ℝ)) ≤ (N : ℝ) ^ (1 + ε)) := by
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hK, hpowers⟩ := AsymmetricKernelPowers.few_typed C δ Dold Dcut hδ
  obtain ⟨Ds, kg, hDs, hgeneral⟩ := AsymmetricComponentHostCount.uniform_dense C δ η Dold Dcut hδ hη
  obtain ⟨ko, hlinear⟩ := AsymmetricComponentHostCount.uniform_linear C δ Dold Dcut (K + 1) hδ
  obtain ⟨Np, hp⟩ := hpowers ko
  obtain ⟨Ng, hg⟩ := AsymmetricKernelPowers.uniform_global C δ hδ
  refine ⟨Ds, kg, ko, K, hDs, hK, ?_⟩
  intro hCoverG hCoverO hCurveG hCurveO
  obtain ⟨AG, _hAG, Nd, hd⟩ := hgeneral hCoverG hCurveG
  obtain ⟨AO, _hAO, No, ho⟩ := hlinear hCoverO
    (fun M ↦ UniformNormalizedCurvePointCount.ordinary_specialization ko M (hCurveO M))
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption ((K : ℝ) * AO + AG) (1 + 2 * δ) (ε - 2 * δ)
    (by dsimp [δ]; linarith)
  refine ⟨max 2 (max Nd (max No (max Np (max Ng Nf)))), by omega, ?_⟩
  intro N hN L H R hcrit hR hnew hamb hH old hold F hF hnon hdense
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let hosts := fun a : ℕ ↦ F.filter fun p ↦ ko ≤ (typed p.1 p.2 L H R hnew hamb (old p.1) a).card
  let S := (Icc 1 K).biUnion hosts
  let T := F \ S
  have hSF : S ⊆ F := by
    intro p hp
    obtain ⟨a, _ha, hp⟩ := mem_biUnion.mp hp
    exact (mem_filter.mp hp).1
  have hTF : T ⊆ F := sdiff_subset
  have hcover : ∀ p ∈ S, ∃ a ∈ Icc 1 K, p ∈ hosts a := by
    intro p hpS
    exact mem_biUnion.mp hpS
  have hhosts : ∀ a ∈ Icc 1 K, ((hosts a).card : ℝ) ≤ AO * (N : ℝ) ^ δ := by
    intro a ha
    have hapos := (mem_Icc.mp ha).1
    have haK := (mem_Icc.mp ha).2
    exact ho N (by omega) L H R hcrit hR hnew hamb hH old hold a (by omega) (by omega)
      (hosts a) (fun p hpS ↦ hF p (mem_filter.mp hpS).1)
      (fun p hpS _ ↦ hnon p (mem_filter.mp hpS).1)
      (fun _ hpS ↦ (mem_filter.mp hpS).2)
  have hS : (S.card : ℝ) ≤ ((K : ℝ) * AO) * (N : ℝ) ^ δ := by
    calc
      _ ≤ ((Icc 1 K).card : ℝ) * (AO * (N : ℝ) ^ δ) :=
        FiniteCoverCount.cardinal_le S (Icc 1 K) hosts _ hcover hhosts
      _ = _ := by rw [Nat.card_Icc, Nat.add_sub_cancel]; ring
  have hT : (T.card : ℝ) ≤ AG * (N : ℝ) ^ (1 / 2 + δ) :=
    hd N (by omega) L H R hcrit hR hnew hamb hH old hold T
      (fun p hpT ↦ hF p (hTF hpT)) (fun p hpT ↦ hnon p (hTF hpT))
      (fun p hpT ↦ hdense p (hTF hpT))
  have hweightS : ∀ p ∈ S, (2 ^ loss H (old p.1) p.2 L : ℝ) ≤ (N : ℝ) ^ (1 + δ) :=
    fun p _hpS ↦ hg N (by omega) L hcrit H p.2 (old p.1)
  have hweightT : ∀ p ∈ T, (2 ^ loss H (old p.1) p.2 L : ℝ) ≤ (N : ℝ) ^ (1 / 2 + δ) := by
    intro p hpT
    obtain ⟨hpF, hpS⟩ := mem_sdiff.mp hpT
    obtain ⟨hx, hy⟩ := hF p hpF
    apply hp N (by omega) L H R hcrit hR hnew hamb hH p.1 hx p.2 hy (old p.1) (hold p.1 hx)
    intro a ha
    by_contra hnot
    apply hpS
    exact mem_biUnion.mpr ⟨a, ha, mem_filter.mpr ⟨hpF, by omega⟩⟩
  have hsumS := DenseWeightedSectorUnderInputs.weighted_card_bound S
    (fun p ↦ (2 ^ loss H (old p.1) p.2 L : ℝ)) (N : ℝ) ((K : ℝ) * AO) δ (1 + δ) hn hS hweightS
  have hsumT := DenseWeightedSectorUnderInputs.weighted_card_bound T
    (fun p ↦ (2 ^ loss H (old p.1) p.2 L : ℝ)) (N : ℝ) AG (1 / 2 + δ) (1 / 2 + δ) hn hT hweightT
  rw [show δ + (1 + δ) = 1 + 2 * δ by ring] at hsumS
  rw [show (1 / 2 + δ) + (1 / 2 + δ) = 1 + 2 * δ by ring] at hsumT
  have hpart := sum_sdiff (f := fun p : ℕ × ℕ ↦ (2 ^ loss H (old p.1) p.2 L : ℝ)) hSF
  change (∑ p ∈ T, (2 ^ loss H (old p.1) p.2 L : ℝ)) + (∑ p ∈ S, (2 ^ loss H (old p.1) p.2 L : ℝ)) = _ at hpart
  have htotal : (∑ p ∈ F, (2 ^ loss H (old p.1) p.2 L : ℝ)) ≤
      ((K : ℝ) * AO + AG) * (N : ℝ) ^ (1 + 2 * δ) := by
    linarith only [hpart, hsumS, hsumT]
  exact htotal.trans (by
    simpa only [show (1 + 2 * δ) + (ε - 2 * δ) = 1 + ε by ring] using hf N (by omega))

end PaperP1.AsymmetricDenseMassUnderInputs
