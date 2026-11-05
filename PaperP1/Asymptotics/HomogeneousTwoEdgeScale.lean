module

public import PaperP1.Asymptotics.TwoGoodPairMass

/-! # A fixed-constant second-moment bound for all raw homogeneous good edges -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousTwoEdgeScale

open Finset PaperP1.Model PaperP1.HomogeneousRunMass PaperP1.HomogeneousChannelMass

theorem uniform_second (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      HomogeneousEdgeInteractions.second L (rawPrincipal N H L) ≤
        K * ((L : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ)) ^ 2 := by
  obtain ⟨NU, _hNU, hu⟩ := TwoGoodPairMass.uniform_homogeneous_second C (1 / 60) (by norm_num)
  obtain ⟨A, hA, NA, _hNA, ha⟩ := uniform_principal_upper C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨A ^ 2 + 1, by positivity, 10 + NU + NA + NG, by omega, ?_⟩
  intro N hN L H hband
  have hL : 1 ≤ L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let B : ℝ := L * (N : ℝ) ^ (-2 / 3 : ℝ)
  have herr : (N : ℝ) ^ (-41 / 30 + 1 / 60 : ℝ) ≤ B ^ 2 := by
    have heq : (N : ℝ) ^ (-4 / 3 : ℝ) = ((N : ℝ) ^ (-2 / 3 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
      congr 1
      norm_num
    calc
      _ ≤ (N : ℝ) ^ (-4 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ ≤ B ^ 2 := by
        rw [heq]
        apply pow_le_pow_left₀ (by positivity)
        have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hLR (Real.rpow_nonneg hn.le (-2 / 3))
  have hmass := ha N (by omega) L H hband
  have hmassnon : 0 ≤ PrimitiveNominalMass.mass (rawPrincipal N H L) L :=
    sum_nonneg (fun e _he ↦ PrimitiveNominalMass.weight_nonneg L e)
  have hmassB : PrimitiveNominalMass.mass (rawPrincipal N H L) L ≤ A * B := by
    simpa only [B, mul_assoc] using hmass
  have hmasssq := pow_le_pow_left₀ hmassnon hmassB 2
  have hsecond := hu N (by omega) L H hband
  change _ ≤ (A ^ 2 + 1) * B ^ 2
  nlinarith only [hsecond, hmasssq, herr]

end PaperP1.HomogeneousTwoEdgeScale
