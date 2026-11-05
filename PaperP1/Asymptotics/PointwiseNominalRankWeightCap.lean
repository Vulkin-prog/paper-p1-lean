module

public import PaperP1.Asymptotics.CriticalPairKernelPowers
public import PaperP1.Model.PrimitiveNominalMass

/-! # A uniform nominal rank-weight bound with a fixed additive allowance -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PointwiseNominalRankWeightCap

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (r : ℕ) (C a R ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ I : Finset ℕ,
      I.card = r → (runRelativeNullity L I : ℝ) ≤ a * ((L + 1 : ℕ) : ℝ) + R →
        PrimitiveNominalMass.weight L I ≤ (N : ℝ) ^ (-(r : ℝ) + a + ε) := by
  obtain ⟨NR, hr⟩ := CriticalPairKernelPowers.power_of_rank C a R (ε / 2) ha (by positivity)
  obtain ⟨NA, habsorb⟩ := HalfCountSchedule.factor_absorption (((2 : ℝ) ^ C) ^ r)
    (-(r : ℝ) + a + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NR + NA, by omega, ?_⟩
  intro N hN L hband I hcard hdim
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprod : ((2 ^ L : ℝ)⁻¹) ^ r ≤ ((2 : ℝ) ^ C / N) ^ r :=
    pow_le_pow_left₀ (by positivity)
      (LocalRigidityConsequences.nominal_marginal_bound (by omega) hband) r
  have hrank : (2 ^ runRelativeNullity L I : ℝ) ≤ (N : ℝ) ^ (a + ε / 2) := by
    apply hr N (by omega) L _ hband
    have hh : 0 ≤ (ε / 4) * ((L + 1 : ℕ) : ℝ) := by positivity
    nlinarith only [hdim, hh]
  change ((2 ^ L : ℝ)⁻¹) ^ I.card * (2 ^ runRelativeNullity L I : ℝ) ≤ _
  rw [hcard]
  calc
    _ ≤ ((2 : ℝ) ^ C / N) ^ r * (N : ℝ) ^ (a + ε / 2) :=
      mul_le_mul hprod hrank (by positivity) (by positivity)
    _ = ((2 : ℝ) ^ C) ^ r * (N : ℝ) ^ (-(r : ℝ) + a + ε / 2) := by
      rw [div_pow, ← Real.rpow_natCast (N : ℝ) r]
      have he : (a + ε / 2) - (r : ℝ) = -(r : ℝ) + a + ε / 2 := by ring
      rw [← he, Real.rpow_sub hn]
      ring
    _ ≤ (N : ℝ) ^ ((-(r : ℝ) + a + ε / 2) + ε / 2) := habsorb N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PointwiseNominalRankWeightCap
