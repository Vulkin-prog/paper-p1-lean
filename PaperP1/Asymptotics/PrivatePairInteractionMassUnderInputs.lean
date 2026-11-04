module

public import PaperP1.Asymptotics.WindowPairNonalignedMassUnderInputs
public import PaperP1.Asymptotics.HomogeneousSharedInteriorTriples
public import PaperP1.Model.PrivatePairInteractions

/-! # Full homogeneous interaction mass of two actual raw good channels

This includes shared vertices and aligned centres. The only conditional
sector is the nonaligned two-subset surface and curve count.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivatePairInteractionMassUnderInputs

open Finset PaperP1.Model PaperP1.Arithmetic PaperP1.PrivatePairInteractions
  PaperP1.HomogeneousRunMass PaperP1.WindowPairInteractionHosts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_bound (a b c d : ℕ) (ha : 0 < a) (hab : a < b) (hint : b < 2 * a) (hcop : a.Coprime b)
    (hc : 0 < c) (hcd : c < d) (hint' : d < 2 * c) (hcop' : c.Coprime d) (hdb : d ≤ b)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds kg ko K : ℕ, 0 < Ds ∧ 1 ≤ K ∧
      (UniformSourceSurfaceCover.UniformCover kg (AsymmetricComponentHostCount.sizeCap (4 * b) (1 / 12)) Ds →
      UniformOrdinarySurfaceCover.UniformCover ko (K + 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + kg) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (ko + 3) M) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H₁ H₂ : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        PrivatePairInteractions.mass N H₁ H₂ a b c d L ≤ (N : ℝ) ^ (-41 / 30 + ε)) := by
  have hb : 3 ≤ b := by omega
  have hd : 3 ≤ d := by omega
  obtain ⟨Ds, kg, ko, K, hDs, hK, hu⟩ := WindowPairNonalignedMassUnderInputs.uniform_bound
    a b c d ha hab hcop hc hcd hcop' hb hd hdb C (ε / 2) (by positivity)
  obtain ⟨NS, _hNS, hS⟩ := HomogeneousSharedInteriorTriples.uniform_mass (max b d) C (ε / 2) (by positivity)
  obtain ⟨NA, _hNA, hA⟩ := ScaledAlignedTripleMass.uniform_extensions {(a, b)} (max b d) (2 * b) 1
    (by intro ab hab'; have heq := mem_singleton.mp hab'; subst ab; exact ⟨ha, hab, hint, hcop, le_max_left b d⟩)
    C (ε / 2) (by positivity)
  obtain ⟨NG, hG⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b + c + d : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨NF, hF⟩ := HalfCountSchedule.factor_absorption 321 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Ds, kg, ko, K, hDs, hK, ?_⟩
  intro hCoverG hCoverO hCurveG hCurveO
  obtain ⟨NU, _hNU, hU⟩ := hu hCoverG hCoverO hCurveG hCurveO
  refine ⟨max 10 (max NS (max NA (max NG (max NF NU)))), by omega, ?_⟩
  intro N hN L H₁ H₂ hcrit
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlarge : (a + b + c + d) * (L + 1) < N := by
    simpa only [pow_one, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_lt] using hG N (by omega) L hcrit
  have hlarge₁ : (a + b) * (L + 1) < N := by nlinarith only [hlarge, Nat.zero_le ((c + d) * (L + 1))]
  have hlarge₂ : (c + d) * (L + 1) < N := by nlinarith only [hlarge, Nat.zero_le ((a + b) * (L + 1))]
  let P := points N H₁ H₂ a b c d L
  let S := P.filter fun p ↦ (family p).card = 3
  let D := P \ S
  let A := D.filter fun p ↦ CompressedTargetAlignment.Aligned (2 * b) (key b d p).1 (key b d p).2 L
  let B := D \ A
  have hSP : S ⊆ P := filter_subset _ _
  have hDP : D ⊆ P := sdiff_subset
  have hAD : A ⊆ D := filter_subset _ _
  have hAP : A ⊆ P := hAD.trans hDP
  have hBD : B ⊆ D := sdiff_subset
  have hBP : B ⊆ P := hBD.trans hDP
  have hsource (T : Finset ((ℕ × ℕ) × (ℕ × ℕ))) (hTP : T ⊆ P) :
      ∀ p ∈ T, p.1 ∈ PrivateChannelSources.goodSources N H₁ a b L ∧ p.2 ∈ PrivateChannelSources.goodSources N H₂ c d L :=
    fun p hp ↦ ⟨(PrivatePairInteractions.source_data (hTP hp)).1, (PrivatePairInteractions.source_data (hTP hp)).2.1⟩
  have hsumS : (∑ p ∈ S, probability L (family p)) ≤ (4 : ℝ) ^ 3 * (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    have he := EncodedPairUnionWeights.weighted_bound S (fun p ↦ edge p.1) (fun p ↦ edge p.2)
      (pair_key_injective (by omega) hab hcd hlarge₁ hlarge₂ S (hsource S hSP)) (S.image family) 3
      (fun p hp ↦ mem_image.mpr ⟨p, hp, rfl⟩) (fun p hp ↦ (mem_filter.mp hp).2.le)
      (probability L) (fun I ↦ (probability_pos L I).le)
    have hm : (∑ I ∈ S.image family, probability L I) ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) := by
      apply hS N (by omega) L hcrit
      intro I hI
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hI
      exact shared_host (by omega) ha hab hint hcop hc hcd hint' hcop' hlarge₁ hlarge₂ (hSP hp) (mem_filter.mp hp).2
    exact he.trans (mul_le_mul_of_nonneg_left hm (by norm_num))
  have hsumA : (∑ p ∈ A, probability L (family p)) ≤ (4 : ℝ) ^ 4 * (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    have hcard (p : (ℕ × ℕ) × (ℕ × ℕ)) (hp : p ∈ A) : (family p).card = 4 := by
      have hnot : (family p).card ≠ 3 := fun hh ↦ (mem_sdiff.mp (hAD hp)).2 (mem_filter.mpr ⟨hAP hp, hh⟩)
      rcases family_data (by omega) hab hcd hlarge₁ hlarge₂ (hAP hp) with h3 | h4
      · exact False.elim (hnot h3.2)
      · exact h4.2
    have he := EncodedPairUnionWeights.weighted_bound A (fun p ↦ edge p.1) (fun p ↦ edge p.2)
      (pair_key_injective (by omega) hab hcd hlarge₁ hlarge₂ A (hsource A hAP))
      (ScaledAlignedTripleMass.extensions {(a, b)} (max b d) (2 * b) 1 N L) 4
      (fun p hp ↦ aligned_host (by omega) hab hcd hlarge₁ hlarge₂ (by omega) (hAP hp) (hcard p hp) (mem_filter.mp hp).2)
      (fun p hp ↦ (hcard p hp).le) (probability L) (fun I ↦ (probability_pos L I).le)
    exact he.trans (mul_le_mul_of_nonneg_left (hA N (by omega) L hcrit) (by norm_num))
  have hsumB : (∑ p ∈ B, probability L (family p)) ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    have hsub : B ⊆ allSources N H₁ H₂ a b c d L := by
      intro p hp
      apply nonaligned_mem (hBP hp)
      intro halign
      exact (mem_sdiff.mp hp).2 (mem_filter.mpr ⟨hBD hp, halign⟩)
    exact ((sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ (probability_pos L (family p)).le)).trans
      (hU N (by omega) L H₁ H₂ hcrit)).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only []))
  have hpartS := sum_sdiff (f := fun p ↦ probability L (family p)) hSP
  have hpartA := sum_sdiff (f := fun p ↦ probability L (family p)) hAD
  have htotal : PrivatePairInteractions.mass N H₁ H₂ a b c d L ≤ 321 * (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    change (∑ p ∈ D, probability L (family p)) + (∑ p ∈ S, probability L (family p)) = _ at hpartS
    change (∑ p ∈ B, probability L (family p)) + (∑ p ∈ A, probability L (family p)) = _ at hpartA
    norm_num at hsumS hsumA
    change (∑ p ∈ P, probability L (family p)) ≤ _
    linarith only [hpartS, hpartA, hsumS, hsumA, hsumB]
  exact htotal.trans (by simpa only [show (-41 / 30 + ε / 2) + ε / 2 = -41 / 30 + ε by ring] using hF N (by omega))

end PaperP1.PrivatePairInteractionMassUnderInputs
