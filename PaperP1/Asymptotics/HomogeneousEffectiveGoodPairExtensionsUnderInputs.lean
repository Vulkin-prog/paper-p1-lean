module

public import PaperP1.Asymptotics.HomogeneousEffectiveConnectedChannelUnderInputs
public import PaperP1.Model.DependentPairCrossingConnected
public import PaperP1.Combinatorics.SingletonExtensionWeights

/-! # Sharp separated one-target mass of actual raw good pairs, including irregular targets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousEffectiveGoodPairExtensionsUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.HomogeneousRunMass PaperP1.SingletonExtensionWeights

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def points (N H a b L : ℕ) : Finset (Finset ℕ × ℕ) :=
  ((PrivateChannelActivity.pairs N H a b L) ×ˢ (dyadicBlock N)).filter fun p ↦
    p.2 ∉ p.1 ∧ SeparatedHomogeneousMass.Separated L (join p) ∧ 0 < OneTargetCrossing.rank p.1 L p.2

def mass (N H a b L : ℕ) : ℝ := ∑ p ∈ points N H a b L, probability L (join p)

theorem union_mem_hosts {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) {p : Finset ℕ × ℕ} (hp : p ∈ points N H a b L) :
    join p ∈ (ConnectedCompressedTripleMassUnderInputs.hosts N a b L).filter
      (SeparatedHomogeneousMass.Separated L) := by
  obtain ⟨hbox, hfresh, hsep, hcross⟩ := mem_filter.mp hp
  obtain ⟨he, hz⟩ := mem_product.mp hbox
  have hedata := PrivateChannelActivity.pair_data hN hab hlarge he
  have hconn := DependentPairCrossingConnected.connected L p.1 p.2 hedata.2
    (PrivateChannelRank.nullity_positive hN ha hab hlarge he) hfresh hcross
  have hcard : (join p).card = 3 := by
    rw [join, union_singleton, card_insert_of_notMem hfresh, hedata.2]
  have hsub : join p ⊆ dyadicBlock N := union_subset hedata.1 (singleton_subset_iff.mpr hz)
  obtain ⟨xy, hxy, hpair⟩ := mem_image.mp he
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨?_, xy, PrivateChannelSources.good_sources_subset_unitSources N H a b L hxy, ?_⟩, hsep⟩
  · exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hsub, hcard⟩, hconn⟩
  · rw [hpair]
    exact subset_union_left

theorem finite_mass {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) :
    mass N H a b L ≤ 3 * HomogeneousEffectiveConnectedChannelUnderInputs.mass N a b L := by
  apply SingletonExtensionWeights.weighted_bound (points N H a b L)
    ((ConnectedCompressedTripleMassUnderInputs.hosts N a b L).filter (SeparatedHomogeneousMass.Separated L)) 3
    (fun _ hp ↦ (mem_filter.mp hp).2.1) (fun _ hp ↦ union_mem_hosts hN ha hab hlarge hp)
    _ (probability L) (fun T ↦ (probability_pos L T).le)
  intro T hT
  obtain ⟨hhost, _⟩ := mem_filter.mp hT
  obtain ⟨hconn, _⟩ := mem_filter.mp hhost
  exact (mem_powersetCard.mp (mem_filter.mp hconn).1).2

theorem uniform_mass (a b : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds kg ko K : ℕ, 0 < Ds ∧ 1 ≤ K ∧
      (UniformSourceSurfaceCover.UniformCover kg
        (AsymmetricComponentHostCount.sizeCap (2 * b + 1) (ε / 256)) Ds →
      UniformOrdinarySurfaceCover.UniformCover ko (K + 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + kg) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (ko + 3) M) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N H a b L ≤ (N : ℝ) ^ (-41 / 30 + ε)) := by
  obtain ⟨Ds, kg, ko, K, hDs, hK, hc⟩ := HomogeneousEffectiveConnectedChannelUnderInputs.uniform_mass
    a b ha hab hb2a hcop C (ε / 2) (by positivity)
  obtain ⟨Nw, hw⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 3 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Ds, kg, ko, K, hDs, hK, ?_⟩
  intro hCoverG hCoverO hCurveG hCurveO
  obtain ⟨Nc, _hNc, hc⟩ := hc (by simpa only [div_div, show (2 : ℝ) * 128 = 256 by norm_num] using hCoverG)
    hCoverO hCurveG hCurveO
  refine ⟨max 4 (max Nc (max Nw Nf)), by omega, ?_⟩
  intro N hN L H hcrit
  have hlarge : (a + b) * (L + 1) < N := by
    have hh := hw N (by omega) L hcrit
    simp only [pow_one] at hh
    exact_mod_cast hh
  calc
    _ ≤ 3 * HomogeneousEffectiveConnectedChannelUnderInputs.mass N a b L := finite_mass (by omega) ha hab hlarge
    _ ≤ 3 * (N : ℝ) ^ (-41 / 30 + ε / 2) := mul_le_mul_of_nonneg_left (hc N (by omega) L hcrit) (by norm_num)
    _ ≤ _ := by
      simpa only [show (-41 / 30 + ε / 2) + ε / 2 = (-41 / 30 : ℝ) + ε by ring] using hf N (by omega)

end PaperP1.HomogeneousEffectiveGoodPairExtensionsUnderInputs
