module

public import PaperP1.Asymptotics.EffectiveCompressedCrossingProfile
public import PaperP1.Model.HomogeneousCompressedCrossing
public import PaperP1.Asymptotics.HomogeneousChannelWeights
public import PaperP1.Asymptotics.HomogeneousLocalMarginalCap

/-! # Sharp homogeneous nonaligned crossing mass on every effective target -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousEffectiveNonalignedMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.CompressedSourceBlocks PaperP1.DyadicEndpointPairs PaperP1.AsymmetricJointWeight
  PaperP1.OriginalCompressedNonalignedMass

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def mass (N a b L : ℕ) (i j : Fin (L + 1)) : ℝ :=
  ∑ p ∈ OriginalCompressedNonalignedMass.points N a b L i j,
    HomogeneousRunMass.probability L {p.1.1, p.1.2, p.2}

def channelMass (N a b L : ℕ) : ℝ :=
  ∑ ij : Fin (L + 1) × Fin (L + 1), mass N a b L ij.1 ij.2

theorem finite_bound {N a b L H : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) (A : ℝ)
    (hcap : ∀ xy ∈ sourcePairs N a b L i j, ∀ z ∈ dyadicBlock N,
      HomogeneousRunMass.probability L {xy.1, xy.2} * HomogeneousRunMass.probability L {z} ≤ A) :
    mass N a b L i j ≤ 2 * A * EffectiveCompressedCrossingProfile.profile N a b L H i j := by
  let P := OriginalCompressedNonalignedMass.points N a b L i j
  let w := fun p : (ℕ × ℕ) × ℕ ↦ AsymmetricCoarseProfile.weight H L
    (block N a b L i j) (CompressedAsymmetricProfile.centreMap b L i p)
  have hpoint : ∀ p ∈ P, HomogeneousRunMass.probability L {p.1.1, p.1.2, p.2} ≤ 2 * A * w p := by
    intro p hp
    obtain ⟨hpP, _hzx, _hzy, hcross⟩ := mem_filter.mp hp
    obtain ⟨hpD, _hnon⟩ := mem_filter.mp hpP
    obtain ⟨hxy, hz⟩ := mem_product.mp hpD
    have hnonneg : 0 ≤ w p := AsymmetricCoarseProfile.weight_nonneg H L _ _
    have hh := HomogeneousCompressedCrossing.finite_bound (H := H) hN ha hb i j hxy p.2 hcross
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcap p.1 hxy p.2 hz) (by norm_num : (0 : ℝ) ≤ 2)) hnonneg)
  calc
    _ ≤ ∑ p ∈ P, 2 * A * w p := sum_le_sum hpoint
    _ = 2 * A * ∑ p ∈ P, w p := (mul_sum _ _ _).symm
    _ = _ := rfl

theorem uniform_bound (a b : ℕ) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → channelMass N a b L ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε) := by
  let M := 2 * (2 : ℝ) ^ C
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨Nc, _hNc, hc⟩ := EffectiveCompressedCrossingProfile.uniform_channel
    a b (2 * b + 1) ha hab.le (by omega) C (ε / 4) (by positivity)
  obtain ⟨Nq, _hNq, hq⟩ := HomogeneousChannelWeights.uniform_pair C (ε / 4) a b ha hab hcop (by positivity)
  obtain ⟨Np, _hNp, hp⟩ := HomogeneousLocalMarginalCap.uniform_cap C
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption (2 * M) (-2 + 1 / (b : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 4 (max Nc (max Nq (max Np Nf))), by omega, ?_⟩
  intro N hN L hcrit
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let H := (2 * b + 1) * (L + 1)
  let A := M * (N : ℝ) ^ (-3 + 1 / (b : ℝ) + ε / 4)
  have hcap : ∀ i j : Fin (L + 1), ∀ xy ∈ sourcePairs N a b L i j, ∀ z ∈ dyadicBlock N,
      HomogeneousRunMass.probability L {xy.1, xy.2} * HomogeneousRunMass.probability L {z} ≤ A := by
    intro i j xy hxy z hz
    calc
      _ ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 4) * (M / N) :=
        mul_le_mul (hq N (by omega) L hcrit xy (unit_source i j hxy)) (hp N (by omega) L hcrit z hz)
          ((HomogeneousRunMass.probability_pos L {z}).le) (Real.rpow_nonneg hNpos.le _)
      _ = _ := by
        dsimp [A]
        rw [show -3 + 1 / (b : ℝ) + ε / 4 = (-2 + 1 / (b : ℝ) + ε / 4) - 1 by ring,
          Real.rpow_sub hNpos, Real.rpow_one]
        ring
  have hfinite : channelMass N a b L ≤ 2 * A * EffectiveCompressedCrossingProfile.channelProfile N a b L H := by
    rw [channelMass, EffectiveCompressedCrossingProfile.channelProfile, mul_sum]
    exact sum_le_sum fun ij _ ↦ finite_bound (H := H) (by omega) ha (by omega) ij.1 ij.2 A (hcap ij.1 ij.2)
  have hprofile := hc N (by omega) L H hcrit le_rfl le_rfl
  calc
    _ ≤ 2 * A * (N : ℝ) ^ (1 + ε / 4) :=
      hfinite.trans (mul_le_mul_of_nonneg_left hprofile (by positivity))
    _ = (2 * M) * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := by
      dsimp [A]
      rw [mul_assoc, mul_assoc, ← Real.rpow_add hNpos,
        show (-3 + 1 / (b : ℝ) + ε / 4) + (1 + ε / 4) = -2 + 1 / (b : ℝ) + ε / 2 by ring]
      dsimp [M]
      ring
    _ ≤ _ := by
      simpa only [show (-2 + 1 / (b : ℝ) + ε / 2) + ε / 2 = -2 + 1 / (b : ℝ) + ε by ring] using hf N (by omega)

end PaperP1.HomogeneousEffectiveNonalignedMass
