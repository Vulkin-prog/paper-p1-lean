module

public import PaperP1.Model.BlockJointIntersection
public import PaperP1.Asymptotics.DependentPairJointMassUnderInputs
public import PaperP1.Asymptotics.CriticalPairKernelPowers

/-! # The low-intersection two-dependent-pair joint sum has the true four-thirds scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LowTwoPairJointMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.FinitePairDeficitInputs

theorem uniform_bound (a C ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 4096)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ∀ H : Finset (Finset ℕ × Finset ℕ),
        (∀ p ∈ H, p.1 ∈ DependentFamilySeeds.dependentFamilies G L 2 ∧
          p.2 ∈ DependentFamilySeeds.dependentFamilies G L 2 ∧ Disjoint p.1 p.2 ∧
          (Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) p.1 ⊓
            span (fun x ↦ squareClassSpace x L) p.2) : ℝ) ≤ a * L) →
        (∑ p ∈ H, infiniteJointMoment L (p.1 ∪ p.2)) ≤ (N : ℝ) ^ (-4 / 3 + a + ε) := by
  obtain ⟨p, hp⟩ := DependentPairJointMassUnderInputs.uniform_bound C (ε / 4) (by positivity)
  obtain ⟨NR, hr⟩ := CriticalPairKernelPowers.power_of_rank C a 0 (ε / 4) ha (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨p, ?_⟩
  intro hgeo
  have hscale : (ε / 4) / 1024 = ε / 4096 := by ring
  obtain ⟨NP, _hNP, hp⟩ := hp (by simpa only [hscale] using hgeo)
  refine ⟨4 + NP + NR + NG, by omega, ?_⟩
  intro N hN L hband G hG H hH
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := DependentFamilySeeds.dependentFamilies G L 2
  have hpair := hp N (by omega) L hband G hG
  have hsum : 0 ≤ ∑ e ∈ P, infiniteJointMoment L e := sum_nonneg fun e _ ↦ infiniteJointMoment_nonneg L e
  have hfinite := BlockJointIntersection.finite_bound L hL P P H ((N : ℝ) ^ (a + ε / 4))
    (Real.rpow_nonneg hn.le _) (by
      intro p hp
      obtain ⟨hleft, hright, hdis, hlow⟩ := hH p hp
      refine ⟨hleft, hright, hdis, hr N (by omega) L _ hband ?_⟩
      simp only [Nat.cast_add, Nat.cast_one]
      have hprod : 0 ≤ ε * (L : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
      nlinarith only [hlow, ha, hε, hprod])
  have hsquare := pow_le_pow_left₀ hsum hpair 2
  have hpow : ((N : ℝ) ^ (-2 / 3 + ε / 4)) ^ 2 = (N : ℝ) ^ (2 * (-2 / 3 + ε / 4)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    ring
  calc
    _ ≤ (N : ℝ) ^ (a + ε / 4) * (∑ e ∈ P, infiniteJointMoment L e) ^ 2 :=
      hfinite.trans_eq (by ring)
    _ ≤ (N : ℝ) ^ (a + ε / 4) * ((N : ℝ) ^ (-2 / 3 + ε / 4)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (Real.rpow_nonneg hn.le _)
    _ = (N : ℝ) ^ ((a + ε / 4) + 2 * (-2 / 3 + ε / 4)) := by rw [hpow, ← Real.rpow_add hn]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])

end PaperP1.LowTwoPairJointMassUnderInputs
