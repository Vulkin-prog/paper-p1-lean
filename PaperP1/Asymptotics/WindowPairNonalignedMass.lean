module

public import PaperP1.Asymptotics.SubsetInteractionMass
public import PaperP1.Asymptotics.CriticalScaledChannelPowers
public import PaperP1.Asymptotics.CompressedPairIntersectionCount
public import PaperP1.Model.WindowPairInteractionHosts
public import PaperP1.Combinatorics.GraphStarWeights

/-! # The actual nonaligned homogeneous mass of two private good pairs

The host count and both point caps are proved from the original windows.
The pinned-support confinement estimate supplies all nonaligned host counts.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WindowPairNonalignedMass

open Finset PaperP1.Model PaperP1.Arithmetic PaperP1.DyadicEndpointPairs
  PaperP1.HomogeneousRunMass PaperP1.WindowPairCentreBlocks PaperP1.WindowPairInteractionHosts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem fixed_offsets (a b c d : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (hc : 0 < c) (hcd : c < d) (hcop' : c.Coprime d) (hb : 3 ≤ b) (hd : 3 ≤ d)
    (hdb : d ≤ b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H₁ H₂ : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ i j k l : Fin (L + 1),
        (∑ p ∈ sources N H₁ H₂ a b c d L i j k l, probability L (family p)) ≤ (N : ℝ) ^ (-5 / 3 + ε) := by
  have hbpos : 0 < b := by omega
  have hdpos : 0 < d := by omega
  obtain ⟨NU, _hNU, hsector⟩ := SubsetInteractionMass.uniform_bound
    (2 * b) (by omega) (CriticalScaledChannelPowers.band C d) (ε / 2) (2 * b) (4 * b) (by positivity)
  obtain ⟨N₁, _hN₁, hp₁⟩ := CriticalScaledChannelPowers.uniform_pair a b d ha hab hcop hb hdpos C (ε / 32) (by positivity)
  obtain ⟨N₂, _hN₂, hp₂⟩ := CriticalScaledChannelPowers.uniform_pair c d d hc hcd hcop' hd hdpos C (ε / 32) (by positivity)
  obtain ⟨NC, _hNC, hcount⟩ := CompressedPairIntersectionCount.fixed_offsets a b c d ha hab.le hc hcd.le C (ε / 16) (by positivity)
  obtain ⟨NA, ha'⟩ := HalfCountSchedule.factor_absorption ((d : ℝ) ^ (-5 / 3 + ε / 2))
    (-5 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max N₁ (max N₂ (max NC (max NA NU)))), by omega, ?_⟩
  intro N hN L H₁ H₂ hcrit i j k l
  have hNpos : 0 < N := by omega
  have hscale : N ≤ d * N := by simpa only [one_mul] using Nat.mul_le_mul_right N (show 1 ≤ d by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hn' : (0 : ℝ) < (d * N : ℕ) := by exact_mod_cast (show 0 < d * N by omega)
  have hn1 : (1 : ℝ) ≤ (d * N : ℕ) := by exact_mod_cast (show 1 ≤ d * N by omega)
  let P := sources N H₁ H₂ a b c d L i j k l
  let F := P.image (key b d)
  let old := block N a b L i j
  let new := block N c d L k l
  let R := 2 * b * (L + 1)
  let H := 4 * b * (L + 1)
  have hold : ∀ X ∈ ExpandedAsymmetricSupportEnvelope.block (d * N) (2 * b), ∀ n ∈ old X,
      |(n : ℤ) - X| ≤ (R : ℤ) := fun _ _ _ hmem ↦ block_distance hNpos hab.le i j hmem
  have hnew : ∀ Y ∈ dyadicBlock (d * N), ∀ n ∈ new Y, |(n : ℤ) - Y| ≤ (R : ℤ) := by
    intro Y _hY n hnnew
    exact (block_distance hNpos hcd.le k l hnnew).trans (by
      exact_mod_cast Nat.mul_le_mul_right (L + 1) (Nat.mul_le_mul_left 2 hdb))
  have hF : ∀ q ∈ F, q.1 ∈ ExpandedAsymmetricSupportEnvelope.block (d * N) (2 * b) ∧ q.2 ∈ dyadicBlock (d * N) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    obtain ⟨hp₁, hp₂, _⟩ := source_data hp
    exact ⟨expanded_centre hdpos hdb (mem_sourcePairs.mp hp₁).1,
      scaled_dyadic hdpos (mem_sourcePairs.mp hp₂).1⟩
  have hnon : ∀ q ∈ F, ¬CompressedTargetAlignment.Aligned (2 * b) q.1 q.2 L := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    exact (source_data hp).2.2.2.2
  have hcard : (F.card : ℝ) ≤ ((d * N : ℕ) : ℝ) ^ (1 + (ε / 2) / 8) := by
    have hPc : P.card ≤ (CompressedPairIntersectionHosts.pairs N a b c d L i j k l).card :=
      card_le_card (filter_subset _ _)
    calc
      _ ≤ (P.card : ℝ) := by exact_mod_cast card_image_le
      _ ≤ ((CompressedPairIntersectionHosts.pairs N a b c d L i j k l).card : ℝ) := by exact_mod_cast hPc
      _ ≤ (N : ℝ) ^ (1 + ε / 16) := hcount N (by omega) L hcrit i j k l
      _ ≤ _ := by
        rw [show (ε / 2) / 8 = ε / 16 by ring]
        exact Real.rpow_le_rpow hn.le (by exact_mod_cast hscale) (by positivity)
  have hcap₁ (p : (ℕ × ℕ) × (ℕ × ℕ)) (hp : p ∈ P) :
      probability L {p.1.1, p.1.2} ≤ ((d * N : ℕ) : ℝ) ^ (-5 / 3 + ε / 32) :=
    hp₁ N (by omega) L H₁ hcrit _ (mem_image.mpr ⟨p.1, (source_data hp).2.2.1, rfl⟩)
  have hcap₂ (p : (ℕ × ℕ) × (ℕ × ℕ)) (hp : p ∈ P) :
      probability L {p.2.1, p.2.2} ≤ ((d * N : ℕ) : ℝ) ^ (-5 / 3 + ε / 32) :=
    hp₂ N (by omega) L H₂ hcrit _ (mem_image.mpr ⟨p.2, (source_data hp).2.2.2.1, rfl⟩)
  have hsingle : ∀ q ∈ F, weight L b d P q ≤ ((d * N : ℕ) : ℝ) ^ (-5 / 3 + (ε / 2) / 8) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    rw [weight_key hNpos ha hbpos hc hdpos i j k l hp]
    exact ((probability_antitone L (subset_union_left : ({p.1.1, p.1.2} : Finset ℕ) ⊆ family p)).trans (hcap₁ p hp)).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε]))
  have hproduct : ∀ q ∈ F, weight L b d P q ≤ ((d * N : ℕ) : ℝ) ^ (-10 / 3 + (ε / 2) / 8) *
      (2 ^ SubsetEvenLoss.loss H (old q.1) (new q.2) : ℝ) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    rw [weight_key hNpos ha hbpos hc hdpos i j k l hp]
    have hprod := mul_le_mul (hcap₁ p hp) (hcap₂ p hp) (probability_pos L _).le (by positivity)
    rw [← Real.rpow_add hn', show (-5 / 3 + ε / 32) + (-5 / 3 + ε / 32) = -10 / 3 + (ε / 2) / 8 by ring] at hprod
    exact (upper_loss (by omega) ha hbpos hc hdpos i j k l (source_data hp).1 (source_data hp).2.1 H).trans
      (mul_le_mul_of_nonneg_right hprod (by positivity))
  have hmass := hsector (d * N) (by omega) L H R (CriticalScaledChannelPowers.critical_band_mul hNpos hdpos hcrit)
    le_rfl (by dsimp [R]; nlinarith only [hbpos, Nat.zero_le L]) (by dsimp [R, H]; nlinarith only []) le_rfl old new hold hnew
    (fun Y _ ↦ block_card hNpos hc hdpos k l Y) F hF hnon hcard (weight L b d P) hsingle hproduct
  rw [sum_eq hNpos ha hbpos hc hdpos i j k l] at hmass
  calc
    _ ≤ ((d * N : ℕ) : ℝ) ^ (-5 / 3 + ε / 2) := hmass
    _ = (d : ℝ) ^ (-5 / 3 + ε / 2) * (N : ℝ) ^ (-5 / 3 + ε / 2) := by rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg d) hn.le]
    _ ≤ _ := by simpa only [show (-5 / 3 + ε / 2) + ε / 2 = -5 / 3 + ε by ring] using ha' N (by omega)

theorem uniform_bound (a b c d : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (hc : 0 < c) (hcd : c < d) (hcop' : c.Coprime d) (hb : 3 ≤ b) (hd : 3 ≤ d)
    (hdb : d ≤ b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H₁ H₂ : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        mass N H₁ H₂ a b c d L ≤ (N : ℝ) ^ (-5 / 3 + ε) := by
  obtain ⟨NU, _hNU, hU⟩ := fixed_offsets a b c d ha hab hcop hc hcd hcop' hb hd hdb C (ε / 2) (by positivity)
  obtain ⟨NS, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NP, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (CriticalBandScale.upperScale ^ 4) 4 (ε / 2) (by positivity)
  refine ⟨max 2 (max NS (max NP NU)), by omega, ?_⟩
  intro N hN L H₁ H₂ hcrit
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoly : ((L + 1 : ℕ) : ℝ) ^ 4 ≤ (N : ℝ) ^ (ε / 2) := by
    calc
      _ ≤ (CriticalBandScale.upperScale * Real.log N) ^ 4 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hs N (by omega) L hcrit).2 4
      _ = CriticalBandScale.upperScale ^ 4 * (Real.log N) ^ 4 := mul_pow _ _ _
      _ ≤ _ := by simpa only [Real.rpow_ofNat] using hp N (by omega)
  calc
    _ ≤ ∑ w : (Fin (L + 1) × Fin (L + 1)) × (Fin (L + 1) × Fin (L + 1)),
        ∑ p ∈ sources N H₁ H₂ a b c d L w.1.1 w.1.2 w.2.1 w.2.2, probability L (family p) := by
      exact (sum_le_sum_of_subset_of_nonneg (all_sources_cover N H₁ H₂ a b c d L)
        (fun p _ _ ↦ (probability_pos L (family p)).le)).trans
        (GraphStarWeights.sum_biUnion_le_nonneg univ _ (fun p ↦ probability L (family p))
          (fun p ↦ (probability_pos L (family p)).le))
    _ ≤ ∑ _w : (Fin (L + 1) × Fin (L + 1)) × (Fin (L + 1) × Fin (L + 1)),
        (N : ℝ) ^ (-5 / 3 + ε / 2) := sum_le_sum (fun w _ ↦ hU N (by omega) L H₁ H₂ hcrit w.1.1 w.1.2 w.2.1 w.2.2)
    _ = ((L + 1 : ℕ) : ℝ) ^ 4 * (N : ℝ) ^ (-5 / 3 + ε / 2) := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-5 / 3 + ε / 2) := mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.WindowPairNonalignedMass
