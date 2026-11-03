module

public import PaperP1.Asymptotics.OriginalWindowFamilyMass
public import PaperP1.Asymptotics.CriticalPairKernelPowers
public import PaperP1.Model.PrimitiveWindowMass

/-! # Uniform actual heterogeneous rank weights with a fixed additive rank allowance -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PointwiseRankWeightCap

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (r : ℕ) (C a R ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ I : Finset ℕ,
      I ⊆ dyadicBlock N → I.card = r →
      (runRelativeNullity L I : ℝ) ≤ a * ((L + 1 : ℕ) : ℝ) + R →
        PrimitiveWindowMass.weight L I ≤ (N : ℝ) ^ (-(r : ℝ) + a + ε) := by
  obtain ⟨K, hK, NM, hm⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NR, hr⟩ := CriticalPairKernelPowers.power_of_rank C a R (ε / 2) ha (by positivity)
  obtain ⟨NA, habsorb⟩ := HalfCountSchedule.factor_absorption (K ^ r)
    (-(r : ℝ) + a + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NM + NR + NA, by omega, ?_⟩
  intro N hN L hband I hIG hcard hdim
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprod : (∏ x ∈ I, infiniteMarginal x L) ≤ (K / N) ^ r := by
    have hh := prod_le_prod₀ (fun x _hx ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      (fun x hx ↦ (hm N (by omega) L x hband (hIG hx)).2)
    exact hh.trans_eq (by rw [prod_const, hcard])
  have hrank : (2 ^ runRelativeNullity L I : ℝ) ≤ (N : ℝ) ^ (a + ε / 2) := by
    apply hr N (by omega) L _ hband
    have hh : 0 ≤ (ε / 4) * ((L + 1 : ℕ) : ℝ) := by positivity
    nlinarith only [hdim, hh]
  calc
    PrimitiveWindowMass.weight L I ≤ (K / N) ^ r * (N : ℝ) ^ (a + ε / 2) :=
      mul_le_mul hprod hrank (by positivity) (by positivity)
    _ = K ^ r * (N : ℝ) ^ (-(r : ℝ) + a + ε / 2) := by
      rw [div_pow, ← Real.rpow_natCast (N : ℝ) r]
      have he : (a + ε / 2) - (r : ℝ) = -(r : ℝ) + a + ε / 2 := by ring
      rw [← he, Real.rpow_sub hn]
      ring
    _ ≤ (N : ℝ) ^ ((-(r : ℝ) + a + ε / 2) + ε / 2) := habsorb N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PointwiseRankWeightCap
