module

public import PaperP1.Asymptotics.SharpFixedChannelNonalignedMassUnderInputs
public import PaperP1.Asymptotics.ConnectedCompressedTripleMassUnderInputs

/-! # Sharp connected triple mass above any fixed actual interior unit channel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpConnectedChannelMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedCompressedTripleMassUnderInputs

theorem uniform_mass (a b : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds kg ko K : ℕ, 0 < Ds ∧ 1 ≤ K ∧
      (UniformSourceSurfaceCover.UniformCover kg
        (AsymmetricComponentHostCount.sizeCap (2 * b + 1) (ε / 128)) Ds →
      UniformOrdinarySurfaceCover.UniformCover ko (K + 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + kg) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (ko + 3) M) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N a b L ≤ (N : ℝ) ^ (-41 / 30 + ε)) := by
  obtain ⟨Ds, kg, ko, K, hDs, hK, hn⟩ := SharpFixedChannelNonalignedMassUnderInputs.uniform_bound
    a b ha hab hcop C (ε / 2) (by positivity)
  obtain ⟨Na, _hNa, haM⟩ := CompressedAlignedTripleMass.uniform_mass {(a, b)} b
    (by intro ab hab'; have heq := mem_singleton.mp hab'; subst ab; exact ⟨ha, hab, hb2a, hcop⟩)
    C (ε / 2) (by positivity)
  obtain ⟨Nw, hw⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 2 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Ds, kg, ko, K, hDs, hK, ?_⟩
  intro hCoverG hCoverO hCurveG hCurveO
  obtain ⟨Nn, _hNn, hn⟩ := hn (by simpa only [div_div, show (2 : ℝ) * 64 = 128 by norm_num] using hCoverG)
    hCoverO hCurveG hCurveO
  refine ⟨max 4 (max Na (max Nw (max Nf Nn))), by omega, ?_⟩
  intro N hN L hcrit
  have hlarge : (a + b) * (L + 1) < N := by
    have hh := hw N (by omega) L hcrit
    simp only [pow_one] at hh
    exact_mod_cast hh
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hA := (haM N (by omega) L hcrit).trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (-41 / 30 : ℝ) + ε / 2 ≤ -41 / 30 + ε / 2))
  have hrecip : 1 / (b : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast (show 3 ≤ b by omega))
  have hN := (hn N (by omega) L hcrit).trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hrecip] : -2 + 1 / (b : ℝ) + ε / 2 ≤ -41 / 30 + ε / 2))
  calc
    _ ≤ 2 * (N : ℝ) ^ (-41 / 30 + ε / 2) := by
      have hh := finite_mass (by omega : 2 ≤ N) ha hab hcop hlarge
      linarith only [hh, hA, hN]
    _ ≤ _ := by
      simpa only [show (-41 / 30 + ε / 2) + ε / 2 = -41 / 30 + ε by ring] using hf N (by omega)

end PaperP1.SharpConnectedChannelMassUnderInputs
