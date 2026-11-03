module

public import PaperP1.Model.PrincipalPositiveCover
public import PaperP1.Asymptotics.AlignedSourcePairMass
public import PaperP1.Asymptotics.NormalizedDefectSourceWeight

/-! # All aligned positive source mass outside the two private channels is residual -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalPositiveResidual

open Finset PaperP1.Model PaperP1.SourcePairPositiveWeight PaperP1.PrincipalPositiveCover

theorem uniform_bound (C ε : ℝ) (D : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      (∑ e ∈ residual N H L, setWeight L e) ≤ (N : ℝ) ^ (6 / 5 + ε) := by
  obtain ⟨N1, _hN1, h1⟩ := AlignedSourcePairMass.uniform_height_one_separated C (ε / 2) (by positivity)
  obtain ⟨N2, _hN2, h2⟩ := AlignedSourcePairMass.uniform_height_two C (ε / 2) (by positivity)
  obtain ⟨N23, _hN23, h23⟩ := NormalizedDefectSourceWeight.uniform_pair_mass C (ε / 2) D 2 3
    (by decide) (by decide) (by decide) (by positivity)
  obtain ⟨N34, _hN34, h34⟩ := NormalizedDefectSourceWeight.uniform_pair_mass C (ε / 2) D 3 4
    (by decide) (by decide) (by decide) (by positivity)
  obtain ⟨NZ, _hNZ, hz⟩ := AlignedSourcePairMass.uniform_zero_family C (ε / 2) (by positivity)
  obtain ⟨N5, _hN5, h5⟩ := AlignedSourcePairMass.uniform_high_family 5 (by decide) C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 4
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C 2 (by norm_num) 4
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 6 (6 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max N1 (max N2 (max N23 (max N34 (max NZ (max N5 (max NG (max NL NF)))))))), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hgeom := hg N (by omega) L hband
  have hheight : 4 ≤ (L + 1) ^ 3 := hgeom.2.1.trans
    (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0))
  have hlarge : 2 * (L + 1) ^ 4 < N := by exact_mod_cast hl N (by omega) L hband
  have hcompare (a : ℝ) (ha : a ≤ 6 / 5) :
      (N : ℝ) ^ (a + ε / 2) ≤ (N : ℝ) ^ (6 / 5 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hh1 := (h1 N (by omega) L hband).trans (hcompare 1 (by norm_num))
  have hh2 := (h2 N (by omega) L hband).trans (hcompare (1 / 2) (by norm_num))
  have hh23 := h23 N (by omega) L H hband (by omega) hH
  have hh34 := h34 N (by omega) L H hband (by omega) hH
  norm_num only [Nat.cast_ofNat] at hh23 hh34
  have hh23' := hh23.trans (hcompare (5 / 6) (by norm_num))
  have hh34' := hh34.trans (hcompare (3 / 4) (by norm_num))
  have hhz := (hz N (by omega) L hband).trans (hcompare 1 (by norm_num))
  have hh5 := h5 N (by omega) L hband
  norm_num only [Nat.cast_ofNat] at hh5
  have hh5' : (∑ e ∈ AlignedChannelFamilies.families N L 5, setWeight L e) ≤
      (N : ℝ) ^ (6 / 5 + ε / 2) := hh5
  have hfinite := finite_residual_bound (H := H) (by omega : 2 ≤ N) hheight hlarge
  calc
    _ ≤ 6 * (N : ℝ) ^ (6 / 5 + ε / 2) := by
      linarith only [hfinite, hh1, hh2, hh23', hh34', hhz, hh5']
    _ ≤ (N : ℝ) ^ ((6 / 5 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PrincipalPositiveResidual
