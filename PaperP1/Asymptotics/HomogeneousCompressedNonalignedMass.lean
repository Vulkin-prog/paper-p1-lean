module

public import PaperP1.Asymptotics.CompressedAsymmetricProfile
public import PaperP1.Model.HomogeneousCompressedCrossing
public import PaperP1.Asymptotics.OriginalCompressedNonalignedMass
public import PaperP1.Asymptotics.HomogeneousChannelWeights

/-! # Four-thirds homogeneous mass for nonaligned compressed crossings with regular targets

Every unit-offset pair and every actual source-pair multiplicity is retained.
The internally proved coarse asymmetric profile supplies the complete estimate.
Every true source multiplicity and original target restriction is retained.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousCompressedNonalignedMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.CompressedSourceBlocks PaperP1.DyadicEndpointPairs PaperP1.AsymmetricJointWeight

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def points (N a b L : ℕ) (i j : Fin (L + 1)) : Finset ((ℕ × ℕ) × ℕ) :=
  (OriginalCompressedNonalignedMass.points N a b L i j).filter fun p ↦
    p.2 ∈ RegularStarts.regularStarts N L

def mass (N a b L : ℕ) (i j : Fin (L + 1)) : ℝ :=
  ∑ p ∈ points N a b L i j, HomogeneousRunMass.probability L {p.1.1, p.1.2, p.2}

def channelMass (N a b L : ℕ) : ℝ :=
  ∑ ij : Fin (L + 1) × Fin (L + 1), mass N a b L ij.1 ij.2

theorem finite_bound {N a b L H : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) (A : ℝ) (hA : 0 ≤ A)
    (hcap : ∀ xy ∈ sourcePairs N a b L i j, ∀ z ∈ RegularStarts.regularStarts N L,
      HomogeneousRunMass.probability L {xy.1, xy.2} * HomogeneousRunMass.probability L {z} ≤ A) :
    mass N a b L i j ≤ 2 * A * CompressedAsymmetricProfile.profile N a b L H i j := by
  let P := points N a b L i j
  let w := fun p : (ℕ × ℕ) × ℕ ↦ AsymmetricCoarseProfile.weight H L
    (CompressedSourceBlocks.block N a b L i j) (CompressedAsymmetricProfile.centreMap b L i p)
  have hpoint : ∀ p ∈ P, HomogeneousRunMass.probability L {p.1.1, p.1.2, p.2} ≤ 2 * A * w p := by
    intro p hp
    obtain ⟨hpOld, hzReg⟩ := mem_filter.mp hp
    obtain ⟨hpP, _hzx, _hzy, hcross⟩ := mem_filter.mp hpOld
    obtain ⟨hpD, _hnon⟩ := mem_filter.mp hpP
    obtain ⟨hxy, _hz⟩ := mem_product.mp hpD
    have hnonneg : 0 ≤ w p := AsymmetricCoarseProfile.weight_nonneg H L _ _
    have hh := HomogeneousCompressedCrossing.finite_bound (H := H) hN ha hb i j hxy p.2 hcross
    have hbound := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcap p.1 hxy p.2 hzReg) (by norm_num : (0 : ℝ) ≤ 2)) hnonneg
    exact hh.trans hbound
  calc
    _ ≤ ∑ p ∈ P, 2 * A * w p := sum_le_sum hpoint
    _ = 2 * A * ∑ p ∈ P, w p := by rw [mul_sum]
    _ ≤ 2 * A * ∑ p ∈ CompressedAsymmetricProfile.points N a b L i j, w p :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg ((filter_subset _ _).trans (filter_subset _ _))
        (fun p _ _ ↦ AsymmetricCoarseProfile.weight_nonneg H L _ _)) (by positivity)
    _ = _ := rfl

theorem uniform_mass (a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (hb : 3 ≤ b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → channelMass N a b L ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  let M := (2 : ℝ) ^ C
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨Nc, _hNc, hc⟩ := CompressedAsymmetricProfile.uniform_channel
    a b (2 * b + 1) ha hab.le (by omega) C (ε / 4) (by positivity)
  obtain ⟨Nq, _hNq, hq⟩ := HomogeneousChannelWeights.uniform_pair C (ε / 4) a b ha hab hcop (by positivity)
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption (2 * M) (-4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 4 (max Nc (max Nq Nf)), by omega, ?_⟩
  intro N hN L hcrit
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let H := (2 * b + 1) * (L + 1)
  let A := M * (N : ℝ) ^ (-3 + 1 / (b : ℝ) + ε / 4)
  have hA : 0 ≤ A := mul_nonneg hM.le (Real.rpow_nonneg hNpos.le _)
  have hcap : ∀ i j : Fin (L + 1), ∀ xy ∈ sourcePairs N a b L i j, ∀ z ∈ RegularStarts.regularStarts N L,
      HomogeneousRunMass.probability L {xy.1, xy.2} * HomogeneousRunMass.probability L {z} ≤ A := by
    intro i j xy hxy z hz
    calc
      _ ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 4) * (M / N) :=
        mul_le_mul (hq N (by omega) L hcrit xy (OriginalCompressedNonalignedMass.unit_source i j hxy)) (by rw [HomogeneousChannelWeights.regular_singleton hz]; exact LocalRigidityConsequences.nominal_marginal_bound (by omega) hcrit)
          (HomogeneousRunMass.probability_pos L {z}).le (Real.rpow_nonneg hNpos.le _)
      _ = _ := by
        dsimp [A]
        rw [show -3 + 1 / (b : ℝ) + ε / 4 = (-2 + 1 / (b : ℝ) + ε / 4) - 1 by ring,
          Real.rpow_sub hNpos, Real.rpow_one]
        ring
  have hfinite : channelMass N a b L ≤ 2 * A * CompressedAsymmetricProfile.channelProfile N a b L H := by
    rw [channelMass, CompressedAsymmetricProfile.channelProfile, mul_sum]
    exact sum_le_sum fun ij _ ↦ finite_bound (H := H) (by omega) ha (by omega) ij.1 ij.2 A hA (hcap ij.1 ij.2)
  have hprofile := hc N (by omega) L H hcrit le_rfl le_rfl
  have hrecip : 1 / (b : ℝ) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast hb)
  calc
    _ ≤ 2 * A * (N : ℝ) ^ (4 / 3 + ε / 4) :=
      hfinite.trans (mul_le_mul_of_nonneg_left hprofile (by positivity))
    _ = (2 * M) * (N : ℝ) ^ (-5 / 3 + 1 / (b : ℝ) + ε / 2) := by
      dsimp [A]
      rw [mul_assoc, mul_assoc, ← Real.rpow_add hNpos,
        show (-3 + 1 / (b : ℝ) + ε / 4) + (4 / 3 + ε / 4) = -5 / 3 + 1 / (b : ℝ) + ε / 2 by ring]
      dsimp [M]
      ring
    _ ≤ (2 * M) * (N : ℝ) ^ (-4 / 3 + ε / 2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hrecip])) (by positivity)
    _ ≤ _ := by
      simpa only [show (-4 / 3 + ε / 2) + ε / 2 = -4 / 3 + ε by ring] using hf N (by omega)

end PaperP1.HomogeneousCompressedNonalignedMass
