module

public import PaperP1.Asymptotics.SharpFixedChannelNonalignedMass
public import PaperP1.Asymptotics.ConnectedCompressedTripleMass

/-! # Sharp connected triple mass above any fixed actual interior unit channel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpConnectedChannelMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedCompressedTripleMass

theorem uniform_mass (a b : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N a b L ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨Nn, _hNn, hn⟩ := SharpFixedChannelNonalignedMass.uniform_bound
    a b ha hab hcop C (ε / 2) (by positivity)
  obtain ⟨Na, _hNa, haM⟩ := CompressedAlignedTripleMass.uniform_mass {(a, b)} b
    (by intro ab hab'; have heq := mem_singleton.mp hab'; subst ab; exact ⟨ha, hab, hb2a, hcop⟩)
    C (ε / 2) (by positivity)
  obtain ⟨Nw, hw⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 2 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
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

end PaperP1.SharpConnectedChannelMass
