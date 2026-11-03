module

public import PaperP1.Asymptotics.OriginalWindowFamilyMass
public import PaperP1.Asymptotics.CriticalPairKernelPowers
public import PaperP1.Model.PrimitiveWindowMass

/-! # An unconditional actual probability cap at every fixed cardinality and effective rank

The finite coefficient is the actual heterogeneous product. Compatibility and
positive marginals are not additional premises.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PointwiseJointRankCap

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (r : ℕ) (C σ ε : ℝ) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ I : Finset ℕ,
      I ⊆ dyadicBlock N → I.card = r → (runRelativeNullity L I : ℝ) ≤ σ * L →
        infiniteJointMoment L I ≤ (N : ℝ) ^ (-(r : ℝ) + σ + ε) := by
  obtain ⟨K, hK, NM, hm⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NR, hr⟩ := CriticalPairKernelPowers.power_of_rank C σ 0 (ε / 2) hσ (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (K ^ r)
    (-(r : ℝ) + σ + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NM + NR + NG + NA, by omega, ?_⟩
  intro N hN L hband I hIG hcard hdim
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  have hprod : (∏ x ∈ I, infiniteMarginal x L) ≤ (K / N) ^ r := by
    have hh := prod_le_prod₀ (fun x _hx ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      (fun x hx ↦ (hm N (by omega) L x hband (hIG hx)).2)
    exact hh.trans_eq (by rw [prod_const, hcard])
  have hrank : (2 ^ runRelativeNullity L I : ℝ) ≤ (N : ℝ) ^ (σ + ε / 2) := by
    apply hr N (by omega) L _ hband
    push_cast
    have hnL : 0 ≤ (ε / 4) * (L : ℝ) := by positivity
    nlinarith only [hdim, hσ, hε, hnL]
  calc
    _ ≤ PrimitiveWindowMass.weight L I := PrimitiveWindowMass.joint_le_weight L hL I
    _ ≤ (K / N) ^ r * (N : ℝ) ^ (σ + ε / 2) :=
      mul_le_mul hprod hrank (by positivity) (by positivity)
    _ = K ^ r * (N : ℝ) ^ (-(r : ℝ) + σ + ε / 2) := by
      rw [div_pow, ← Real.rpow_natCast (N : ℝ) r]
      have he : (σ + ε / 2) - (r : ℝ) = -(r : ℝ) + σ + ε / 2 := by ring
      rw [← he, Real.rpow_sub hn]
      ring
    _ ≤ (N : ℝ) ^ ((-(r : ℝ) + σ + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PointwiseJointRankCap
