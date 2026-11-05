module

public import PaperP1.Asymptotics.HomogeneousConnectedTripleMass
public import PaperP1.Model.DependentPairCrossingConnected
public import PaperP1.Combinatorics.SingletonExtensionWeights

/-! # The actual source-edge/target sums in companion T1.12(2), without affine compatibility -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousGoodPairExtensions

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.HomogeneousRunMass PaperP1.SingletonExtensionWeights

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def points (N H a b L : ℕ) : Finset (Finset ℕ × ℕ) :=
  ((PrivateChannelActivity.pairs N H a b L) ×ˢ (RegularStarts.regularStarts N L)).filter fun p ↦
    p.2 ∉ p.1 ∧ SeparatedHomogeneousMass.Separated L (join p) ∧
      0 < OneTargetCrossing.rank p.1 L p.2

def mass (N H a b L : ℕ) : ℝ := ∑ p ∈ points N H a b L, probability L (join p)

theorem union_mem_hosts {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) {p : Finset ℕ × ℕ} (hp : p ∈ points N H a b L) :
    join p ∈ (HomogeneousConnectedTripleMass.hosts N a b L).filter
      (SeparatedHomogeneousMass.Separated L) := by
  obtain ⟨hbox, hfresh, hsep, hcross⟩ := mem_filter.mp hp
  obtain ⟨he, hz⟩ := mem_product.mp hbox
  have hedata := PrivateChannelActivity.pair_data hN hab hlarge he
  have hereg := PrivateChannelRank.regular hN ha hab he
  have hconn := DependentPairCrossingConnected.connected L p.1 p.2 hedata.2
    (PrivateChannelRank.nullity_positive hN ha hab hlarge he) hfresh hcross
  have hcard : (join p).card = 3 := by
    rw [join, union_singleton, card_insert_of_notMem hfresh, hedata.2]
  have hreg : join p ⊆ RegularStarts.regularStarts N L :=
    union_subset hereg (singleton_subset_iff.mpr hz)
  obtain ⟨xy, hxy, hpair⟩ := mem_image.mp he
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨?_, hreg⟩, hsep⟩
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hreg.trans (RegularStarts.regularStarts_subset N L), hcard⟩, hconn⟩,
    xy, PrivateChannelSources.good_sources_subset_unitSources N H a b L hxy, ?_⟩
  rw [hpair]
  exact subset_union_left

theorem finite_mass {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) :
    mass N H a b L ≤ 3 * HomogeneousConnectedTripleMass.mass N a b L := by
  apply SingletonExtensionWeights.weighted_bound (points N H a b L)
    ((HomogeneousConnectedTripleMass.hosts N a b L).filter (SeparatedHomogeneousMass.Separated L)) 3
    (fun _ hp ↦ (mem_filter.mp hp).2.1) (fun _ hp ↦ union_mem_hosts hN ha hab hlarge hp)
    _ (probability L) (fun T ↦ (probability_pos L T).le)
  intro T hT
  obtain ⟨h0, _⟩ := mem_filter.mp hT
  obtain ⟨h1, _⟩ := mem_filter.mp h0
  obtain ⟨h2, _⟩ := mem_filter.mp h1
  exact (mem_powersetCard.mp (mem_filter.mp h2).1).2

theorem uniform_mass (a b : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N H a b L ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨Nc, _hNc, hc⟩ := HomogeneousConnectedTripleMass.uniform_mass
    a b ha hab hb2a hcop C (ε / 2) (by positivity)
  obtain ⟨Nw, hw⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 3 (-4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 4 (max Nc (max Nw Nf)), by omega, ?_⟩
  intro N hN L H hcrit
  have hlarge : (a + b) * (L + 1) < N := by
    have hh := hw N (by omega) L hcrit
    simp only [pow_one] at hh
    exact_mod_cast hh
  calc
    _ ≤ 3 * HomogeneousConnectedTripleMass.mass N a b L := finite_mass (by omega) ha hab hlarge
    _ ≤ 3 * (N : ℝ) ^ (-4 / 3 + ε / 2) := mul_le_mul_of_nonneg_left (hc N (by omega) L hcrit) (by norm_num)
    _ ≤ _ := by
      simpa only [show (-4 / 3 + ε / 2) + ε / 2 = (-4 / 3 : ℝ) + ε by ring] using hf N (by omega)

def nominalMass (N H a b L : ℕ) : ℝ :=
  ∑ p ∈ points N H a b L, PrimitiveNominalMass.weight L (join p)

theorem nominal_mass_eq {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b) :
    nominalMass N H a b L = mass N H a b L := by
  apply sum_congr rfl
  intro p hp
  obtain ⟨hbox, _⟩ := mem_filter.mp hp
  obtain ⟨he, hz⟩ := mem_product.mp hbox
  exact (regular_weight (union_subset (PrivateChannelRank.regular hN ha hab he)
    (singleton_subset_iff.mpr hz))).symm

theorem uniform_nominal_mass (a b : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (mass N H a b L ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
          nominalMass N H a b L ≤ (N : ℝ) ^ (-4 / 3 + ε)) := by
  obtain ⟨N₀, hN₀, hu⟩ := uniform_mass a b ha hab hb2a hcop C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L H hband
  have hh := hu N hN L H hband
  exact ⟨hh, by rw [nominal_mass_eq (by omega) ha hab]; exact hh⟩

theorem companion_T1_12_channel23 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (mass N H 2 3 L ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
          nominalMass N H 2 3 L ≤ (N : ℝ) ^ (-4 / 3 + ε)) := by
  obtain ⟨N₀, hN₀, hu⟩ := uniform_nominal_mass 2 3 (by decide) (by decide) (by decide) (by decide) C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L H hband
  exact hu N hN L H hband

theorem companion_T1_12_channel34 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (mass N H 3 4 L ≤ (N : ℝ) ^ (-5 / 4 + ε) ∧
          nominalMass N H 3 4 L ≤ (N : ℝ) ^ (-5 / 4 + ε)) := by
  obtain ⟨N₀, hN₀, hu⟩ := uniform_nominal_mass 3 4 (by decide) (by decide) (by decide) (by decide) C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L H hband
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp : (N : ℝ) ^ (-4 / 3 + ε) ≤ (N : ℝ) ^ (-5 / 4 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  exact ⟨(hu N hN L H hband).1.trans hp, (hu N hN L H hband).2.trans hp⟩

end PaperP1.HomogeneousGoodPairExtensions
