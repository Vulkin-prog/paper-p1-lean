module

public import PaperP1.Asymptotics.SubsetKernelPowers
public import PaperP1.Asymptotics.DenseWeightedSectorUnderInputs

/-! # A finite two-subset interaction sector with the good-pair weight scales

The source and joint point bounds and the actual host count remain explicit
arguments here. Applying this counting theorem to original good pairs is a
separate obligation; this module does not assert the manuscript theorem.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetInteractionMassUnderInputs

open Finset PaperP1.Model PaperP1.SubsetEvenLoss PaperP1.SubsetComponentHostData

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_bound (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (Dwidth Dcut : ℕ) (hε : 0 < ε) :
    ∃ Ds kg ko K : ℕ, 0 < Ds ∧ 1 ≤ K ∧
      (UniformSourceSurfaceCover.UniformCover kg (AsymmetricComponentHostCount.sizeCap Dcut (1 / 12)) Ds →
      UniformOrdinarySurfaceCover.UniformCover ko (K + 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + kg) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (ko + 3) M) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H R : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dwidth * (L + 1) →
      1 ≤ R → 2 * R ≤ H → H ≤ Dcut * (L + 1) → ∀ old new : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) →
      (∀ y ∈ dyadicBlock N, ∀ n ∈ new y, |(n : ℤ) - y| ≤ (R : ℤ)) →
      (∀ y ∈ dyadicBlock N, (new y).card ≤ 2 * (L + 1)) →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ ExpandedAsymmetricSupportEnvelope.block N Q ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned Dwidth p.1 p.2 L) →
      (F.card : ℝ) ≤ (N : ℝ) ^ (1 + ε / 8) → ∀ w : ℕ × ℕ → ℝ,
      (∀ p ∈ F, w p ≤ (N : ℝ) ^ (-5 / 3 + ε / 8)) →
      (∀ p ∈ F, w p ≤ (N : ℝ) ^ (-10 / 3 + ε / 8) * (2 ^ loss H (old p.1) (new p.2) : ℝ)) →
      (∑ p ∈ F, w p) ≤ (N : ℝ) ^ (-5 / 3 + ε)) := by
  let δ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hK, hpowers⟩ := SubsetKernelPowers.few_typed Q C δ Dwidth Dcut hδ
  obtain ⟨Ds, kg, hDs, hgeneral⟩ := SubsetComponentHostCount.uniform_dense Q hQ C δ (1 / 12) Dwidth Dcut hδ (by norm_num)
  obtain ⟨ko, hlinear⟩ := SubsetComponentHostCount.uniform_linear Q hQ C δ Dwidth Dcut (K + 1) hδ
  obtain ⟨Np, hp⟩ := hpowers ko
  obtain ⟨Nl, hl⟩ := SubsetKernelPowers.few_components Q C (1 / 12) δ Dwidth Dcut (by norm_num) hδ
  refine ⟨Ds, kg, ko, K, hDs, hK, ?_⟩
  intro hCoverG hCoverO hCurveG hCurveO
  obtain ⟨AG, hAG, Ng, hg⟩ := hgeneral hCoverG hCurveG
  obtain ⟨AO, hAO, No, ho⟩ := hlinear hCoverO
    (fun M ↦ UniformNormalizedCurvePointCount.ordinary_specialization ko M (hCurveO M))
  obtain ⟨Na, ha⟩ := HalfCountSchedule.factor_absorption (1 + (K : ℝ) * AO + AG)
    (-5 / 3 + 3 * δ) (ε - 3 * δ) (by dsimp [δ]; linarith only [hε])
  refine ⟨max 2 (max Np (max Nl (max Ng (max No Na)))), by omega, ?_⟩
  intro N hN L H R hcrit hR hRpos hamb hH old new hold hnew hcardNew F hF hnon hcard w hSingle hProduct
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := F.filter fun p ↦ ((nontrivial p.1 p.2 H R (old p.1) (new p.2)).card : ℝ) ≤ (1 / 12) * ((L + 1 : ℕ) : ℝ)
  let D := F \ P
  let hosts := fun a : ℕ ↦ D.filter fun p ↦ ko ≤ (typed p.1 p.2 H R (old p.1) (new p.2) a).card
  let S := (Icc 1 K).biUnion hosts
  let T := D \ S
  have hPF : P ⊆ F := filter_subset _ _
  have hDF : D ⊆ F := sdiff_subset
  have hSD : S ⊆ D := by
    intro p hpS
    obtain ⟨a, _ha, hpD⟩ := mem_biUnion.mp hpS
    exact (mem_filter.mp hpD).1
  have hSF : S ⊆ F := hSD.trans hDF
  have hTD : T ⊆ D := sdiff_subset
  have hTF : T ⊆ F := hTD.trans hDF
  have hDense : ∀ p ∈ D, (1 / 12 : ℝ) * ((L + 1 : ℕ) : ℝ) ≤ (nontrivial p.1 p.2 H R (old p.1) (new p.2)).card := by
    intro p hpD
    obtain ⟨hpF, hpP⟩ := mem_sdiff.mp hpD
    have hn : ¬((nontrivial p.1 p.2 H R (old p.1) (new p.2)).card : ℝ) ≤ (1 / 12) * ((L + 1 : ℕ) : ℝ) :=
      fun hh ↦ hpP (mem_filter.mpr ⟨hpF, hh⟩)
    exact (not_le.mp hn).le
  have hPcard : (P.card : ℝ) ≤ 1 * (N : ℝ) ^ (1 + δ) := by
    exact (show (P.card : ℝ) ≤ F.card by exact_mod_cast card_le_card hPF).trans (by simpa only [one_mul] using hcard)
  have hPweight : ∀ p ∈ P, w p ≤ (N : ℝ) ^ (-10 / 3 + 1 / 12 + 2 * δ) := by
    intro p hpP
    obtain ⟨hx, hy⟩ := hF p (hPF hpP)
    have hpow := hl N (by omega) L H R hcrit hR hamb hH p.1 hx p.2 hy
      (old p.1) (new p.2) (hold p.1 hx) (hnew p.2 hy) (mem_filter.mp hpP).2
    calc
      _ ≤ (N : ℝ) ^ (-10 / 3 + δ) * (N : ℝ) ^ (1 / 12 + δ) :=
        (hProduct p (hPF hpP)).trans (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  have hsumP := DenseWeightedSectorUnderInputs.weighted_card_bound P w (N : ℝ) 1 (1 + δ)
    (-10 / 3 + 1 / 12 + 2 * δ) hn hPcard hPweight
  rw [one_mul, show (1 + δ) + (-10 / 3 + 1 / 12 + 2 * δ) = -9 / 4 + 3 * δ by ring] at hsumP
  have hsumP' : (∑ p ∈ P, w p) ≤ (N : ℝ) ^ (-5 / 3 + 3 * δ) :=
    hsumP.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hhosts : ∀ a ∈ Icc 1 K, ((hosts a).card : ℝ) ≤ AO * (N : ℝ) ^ δ := by
    intro a haK
    exact ho N (by omega) L H R hcrit hR hRpos hH old new hold hnew a
      (by have hh := (mem_Icc.mp haK).1; omega) (by have hh := (mem_Icc.mp haK).2; omega)
      (hosts a) (fun p hpD ↦ hF p (hDF (mem_filter.mp hpD).1))
      (fun p hpD _ ↦ hnon p (hDF (mem_filter.mp hpD).1)) (fun _ hpD ↦ (mem_filter.mp hpD).2)
  have hScard : (S.card : ℝ) ≤ ((K : ℝ) * AO) * (N : ℝ) ^ δ := by
    have hc := FiniteCoverCount.cardinal_le S (Icc 1 K) hosts _ (fun p hpS ↦ mem_biUnion.mp hpS) hhosts
    simpa only [Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_id, mul_assoc] using hc
  have hsumS := DenseWeightedSectorUnderInputs.weighted_card_bound S w (N : ℝ) ((K : ℝ) * AO) δ (-5 / 3 + δ)
    hn hScard (fun p hpS ↦ hSingle p (hSF hpS))
  rw [show δ + (-5 / 3 + δ) = -5 / 3 + 2 * δ by ring] at hsumS
  have hsumS' : (∑ p ∈ S, w p) ≤ ((K : ℝ) * AO) * (N : ℝ) ^ (-5 / 3 + 3 * δ) :=
    hsumS.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ]))
      (mul_nonneg (Nat.cast_nonneg _) hAO.le))
  have hTcard : (T.card : ℝ) ≤ AG * (N : ℝ) ^ (1 / 2 + δ) :=
    hg N (by omega) L H R hcrit hR hRpos hH old new hold hnew T
      (fun p hpT ↦ hF p (hTF hpT)) (fun p hpT ↦ hnon p (hTF hpT)) (fun p hpT ↦ hDense p (hTD hpT))
  have hTweight : ∀ p ∈ T, w p ≤ (N : ℝ) ^ (-7 / 3 + 2 * δ) := by
    intro p hpT
    obtain ⟨hx, hy⟩ := hF p (hTF hpT)
    have hpow : (2 ^ loss H (old p.1) (new p.2) : ℝ) ≤ (N : ℝ) ^ (1 + δ) := by
      apply hp N (by omega) L H R hcrit hR hamb hH p.1 hx p.2 hy
        (old p.1) (new p.2) (hold p.1 hx) (hnew p.2 hy) (hcardNew p.2 hy)
      intro a haK
      by_contra hnot
      apply (mem_sdiff.mp hpT).2
      exact mem_biUnion.mpr ⟨a, haK, mem_filter.mpr ⟨hTD hpT, by omega⟩⟩
    calc
      _ ≤ (N : ℝ) ^ (-10 / 3 + δ) * (N : ℝ) ^ (1 + δ) :=
        (hProduct p (hTF hpT)).trans (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  have hsumT := DenseWeightedSectorUnderInputs.weighted_card_bound T w (N : ℝ) AG (1 / 2 + δ)
    (-7 / 3 + 2 * δ) hn hTcard hTweight
  rw [show (1 / 2 + δ) + (-7 / 3 + 2 * δ) = -11 / 6 + 3 * δ by ring] at hsumT
  have hsumT' : (∑ p ∈ T, w p) ≤ AG * (N : ℝ) ^ (-5 / 3 + 3 * δ) :=
    hsumT.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) hAG.le)
  have hpartP := sum_sdiff (f := w) hPF
  have hpartS := sum_sdiff (f := w) hSD
  have htotal : (∑ p ∈ F, w p) ≤ (1 + (K : ℝ) * AO + AG) * (N : ℝ) ^ (-5 / 3 + 3 * δ) := by
    change (∑ p ∈ D, w p) + (∑ p ∈ P, w p) = _ at hpartP
    change (∑ p ∈ T, w p) + (∑ p ∈ S, w p) = _ at hpartS
    nlinarith only [hpartP, hpartS, hsumP', hsumS', hsumT']
  exact htotal.trans (by
    simpa only [show (-5 / 3 + 3 * δ) + (ε - 3 * δ) = -5 / 3 + ε by ring] using ha N (by omega))

end PaperP1.SubsetInteractionMassUnderInputs
