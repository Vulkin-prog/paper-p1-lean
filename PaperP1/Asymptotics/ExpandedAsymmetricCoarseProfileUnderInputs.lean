module

public import PaperP1.Asymptotics.ExpandedAsymmetricDenseMassUnderInputs
public import PaperP1.Asymptotics.AsymmetricCoarseProfileUnderInputs
public import PaperP1.Asymptotics.ExpandedAsymmetricSparseSupport

/-! # A coarse asymmetric weighted profile with the necessary enlarged alignment radius

The exponent 4/3 is sufficient for some downstream budgets, but is weaker
than the corrected companion target 31/24. The old sets are completely
arbitrary inside the stated interval; their possible choices are not counted.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExpandedAsymmetricCoarseProfileUnderInputs

open Finset PaperP1.Model PaperP1.AsymmetricEvenLoss PaperP1.AsymmetricComponentHostData
  PaperP1.AsymmetricCoarseProfileUnderInputs

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def nonalignedPairs (N Q L Dold : ℕ) : Finset (ℕ × ℕ) :=
  ((ExpandedAsymmetricSupportEnvelope.block N Q) ×ˢ (dyadicBlock N)).filter fun p ↦
    ¬CompressedTargetAlignment.Aligned Dold p.1 p.2 L

def profile (N Q L H Dold : ℕ) (old : ℕ → Finset ℕ) : ℝ :=
  ∑ p ∈ nonalignedPairs N Q L Dold, weight H L old p

theorem uniform_profile (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (Dold Dcut : ℕ) (hDold : 1 ≤ Dold) (hε : 0 < ε) :
    ∃ Ds kg ko K : ℕ, 0 < Ds ∧ 1 ≤ K ∧
      (UniformSourceSurfaceCover.UniformCover kg
        (AsymmetricComponentHostCount.sizeCap Dcut (ε / 8)) Ds →
      UniformOrdinarySurfaceCover.UniformCover ko (K + 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + kg) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (ko + 3) M) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (2 * Dold + 1) * (L + 1) ≤ H → H ≤ Dcut * (L + 1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x,
        |(n : ℤ) - x| ≤ ((Dold * (L + 1) : ℕ) : ℤ)) →
      profile N Q L H Dold old ≤ (N : ℝ) ^ (4 / 3 + ε)) := by
  let η := ε / 8
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Ds, kg, ko, K, hDs, hK, hdense⟩ :=
    ExpandedAsymmetricDenseMassUnderInputs.uniform_weight Q hQ C (ε / 2) η Dold Dcut (by positivity) hη
  obtain ⟨Ns, _hNs, hs⟩ := ExpandedAsymmetricSparseSupport.uniform_count Q hQ C η Dold Dcut hDold hη
  obtain ⟨Np, hp⟩ := ExpandedAsymmetricKernelPowers.few_components Q C η η Dold Dcut hη.le hη
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 2 (4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Ds, kg, ko, K, hDs, hK, ?_⟩
  intro hCoverG hCoverO hCurveG hCurveO
  obtain ⟨Nd, _hNd, hd⟩ := hdense hCoverG hCoverO hCurveG hCurveO
  refine ⟨max 4 (max Ns (max Np (max Nf Nd))), by omega, ?_⟩
  intro N hN L H hcrit hHlow hHhigh old hold
  let R := Dold * (L + 1)
  have hnew : L + 1 ≤ R := by simpa only [one_mul] using Nat.mul_le_mul_right (L + 1) hDold
  have hamb : 2 * R ≤ H := by dsimp [R]; nlinarith only [hHlow]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  let F := nonalignedPairs N Q L Dold
  let D := F.filter fun p ↦ η * ((L + 1 : ℕ) : ℝ) ≤
    (nontrivial p.1 p.2 L H R hnew hamb (old p.1)).card
  let T := F \ D
  let S := T.filter fun p ↦ 0 < loss H (old p.1) p.2 L
  have hDF : D ⊆ F := filter_subset _ _
  have hTF : T ⊆ F := sdiff_subset
  have hST : S ⊆ T := filter_subset _ _
  have hF : ∀ p ∈ F, p.1 ∈ ExpandedAsymmetricSupportEnvelope.block N Q ∧ p.2 ∈ dyadicBlock N := by
    intro p hpF
    exact mem_product.mp (mem_filter.mp hpF).1
  have hnon : ∀ p ∈ F, ¬CompressedTargetAlignment.Aligned Dold p.1 p.2 L := by
    intro p hpF
    exact (mem_filter.mp hpF).2
  have hSsupport : S ⊆ ExpandedAsymmetricSupportEnvelope.population N Q L H old := by
    intro p hpS
    obtain ⟨hpT, hpos⟩ := mem_filter.mp hpS
    exact mem_filter.mpr ⟨mem_product.mpr ⟨(hF p (hTF hpT)).1,
      ExpandedAsymmetricSupportEnvelope.dyadic_subset_block hQ (hF p (hTF hpT)).2⟩, hpos⟩
  have hS : (S.card : ℝ) ≤ (N : ℝ) ^ (4 / 3 + η) := by
    have hcard : (S.card : ℝ) ≤ (ExpandedAsymmetricSupportEnvelope.population N Q L H old).card := by
      exact_mod_cast card_le_card hSsupport
    exact hcard.trans (hs N (by omega) L H hcrit hHlow hHhigh old hold)
  have hweightS : ∀ p ∈ S, weight H L old p ≤ (N : ℝ) ^ (η + η) := by
    intro p hpS
    have hpT := hST hpS
    obtain ⟨hpF, hpD⟩ := mem_sdiff.mp hpT
    obtain ⟨hx, hy⟩ := hF p hpF
    have hc : ((nontrivial p.1 p.2 L H R hnew hamb (old p.1)).card : ℝ) ≤
        η * ((L + 1 : ℕ) : ℝ) := by
      have hh : ¬η * ((L + 1 : ℕ) : ℝ) ≤
          (nontrivial p.1 p.2 L H R hnew hamb (old p.1)).card := by
        intro hh
        exact hpD (mem_filter.mpr ⟨hpF, hh⟩)
      exact (lt_of_not_ge hh).le
    have hh := hp N (by omega) L H R hcrit le_rfl hnew hamb hHhigh
      p.1 hx p.2 (ExpandedAsymmetricSupportEnvelope.dyadic_subset_block hQ hy) (old p.1) (hold p.1 hx) hc
    exact (sub_le_self _ zero_le_one).trans hh
  have hsumS : (∑ p ∈ S, weight H L old p) ≤ (N : ℝ) ^ (4 / 3 + ε / 2) := by
    have hh := DenseWeightedSectorUnderInputs.weighted_card_bound S (weight H L old)
      (N : ℝ) 1 (4 / 3 + η) (η + η) hNpos (by simpa only [one_mul] using hS) hweightS
    rw [one_mul] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [η]; linarith))
  have hsumT : (∑ p ∈ T, weight H L old p) = ∑ p ∈ S, weight H L old p := by
    change (∑ p ∈ T, weight H L old p) = ∑ p ∈ T.filter _, weight H L old p
    rw [sum_filter]
    apply sum_congr rfl
    intro p _hpT
    by_cases hpos : 0 < loss H (old p.1) p.2 L
    · rw [ite_eq_left hpos]
    · have hz : loss H (old p.1) p.2 L = 0 := by omega
      rw [ite_eq_right hpos]
      simp only [weight, hz, pow_zero, sub_self]
  have hsumD : (∑ p ∈ D, weight H L old p) ≤ (N : ℝ) ^ (4 / 3 + ε / 2) := by
    calc
      _ ≤ ∑ p ∈ D, (2 ^ loss H (old p.1) p.2 L : ℝ) :=
        sum_le_sum fun _ _ ↦ sub_le_self _ zero_le_one
      _ ≤ (N : ℝ) ^ (1 + ε / 2) :=
        hd N (by omega) L H R hcrit le_rfl hnew hamb hHhigh old hold D
          (fun p hpD ↦ hF p (hDF hpD)) (fun p hpD ↦ hnon p (hDF hpD))
          (fun _ hpD ↦ (mem_filter.mp hpD).2)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hpart := sum_sdiff (f := weight H L old) hDF
  change (∑ p ∈ T, weight H L old p) + (∑ p ∈ D, weight H L old p) =
    ∑ p ∈ F, weight H L old p at hpart
  change (∑ p ∈ F, weight H L old p) ≤ _
  calc
    _ ≤ 2 * (N : ℝ) ^ (4 / 3 + ε / 2) := by linarith only [hpart, hsumT, hsumS, hsumD]
    _ ≤ _ := by
      simpa only [show (4 / 3 + ε / 2) + ε / 2 = 4 / 3 + ε by ring] using hf N (by omega)

end PaperP1.ExpandedAsymmetricCoarseProfileUnderInputs
