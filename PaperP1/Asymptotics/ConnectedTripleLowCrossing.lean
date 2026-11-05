module

public import PaperP1.Model.ConnectedTripleLowCrossing
public import PaperP1.Asymptotics.SharpPairTargetDeficit
public import PaperP1.Asymptotics.OriginalWindowFamilyMass
public import PaperP1.Asymptotics.CriticalPairKernelPowers

/-! # A small source/complement crossing gives connected triple joint mass N⁻³ᐟ² times its true rank amplification -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedTripleLowCrossing

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.ConnectedWindowFamilies

theorem uniform_bound (a C ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ∀ F : Finset (Finset ℕ), F ⊆ connectedFamilies G L 3 →
        (∀ T ∈ F, ∃ z ∈ T, (Module.finrank F₂ ↥(squareClassSpace z L ⊓
          span (fun x ↦ squareClassSpace x L) (T.erase z)) : ℝ) ≤ a * L) →
        (∑ T ∈ F, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-3 / 2 + a + ε) := by
  obtain ⟨NP, _hNP, hp⟩ := SharpPairTargetDeficit.article_11_1 C (ε / 4) (by positivity)
  obtain ⟨NI, hi⟩ := OriginalWindowFamilyMass.article_10_2 3 (by decide) C (ε / 4) (by positivity)
  obtain ⟨NR, hr⟩ := CriticalPairKernelPowers.power_of_rank C a 0 (ε / 4) ha (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-3 / 2 + ε / 4) (ε / 4) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨4 + NP + NI + NR + NF + NG, by omega, ?_⟩
  intro N hN L hband G hG F hF hlow
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdef := (hp N (by omega) L hband G hG).1
  have hind : FamilyIndependentMass.independentMass (connectedFamilies G L 3) L ≤ (N : ℝ) ^ (-3 / 2 + ε / 4) := by
    simpa only [Nat.cast_ofNat] using (hi N (by omega) L G hband hG).2.2.1
  have hsum : IndependentTargetDeficit.deficit G L +
      FamilyIndependentMass.independentMass (connectedFamilies G L 3) L ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    have hfactor : 2 * (N : ℝ) ^ (-3 / 2 + ε / 4) ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) := by
      convert hf N (by omega) using 1
      congr 1
      ring
    linarith only [hdef, hind, hfactor]
  have hfinite := ConnectedTripleLowCrossing.finite_bound G L hL F hF ((N : ℝ) ^ (a + ε / 4))
    (Real.rpow_nonneg hn.le _) (by
      intro T hT
      obtain ⟨z, hz, hd⟩ := hlow T hT
      refine ⟨z, hz, hr N (by omega) L _ hband ?_⟩
      simp only [Nat.cast_add, Nat.cast_one]
      have hprod : 0 ≤ ε * (L : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg _)
      nlinarith only [hd, ha, hε, hprod])
  calc
    _ ≤ (N : ℝ) ^ (a + ε / 4) * (N : ℝ) ^ (-3 / 2 + ε / 2) :=
      hfinite.trans (mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hn.le _))
    _ = (N : ℝ) ^ ((a + ε / 4) + (-3 / 2 + ε / 2)) := (Real.rpow_add hn _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])

end PaperP1.ConnectedTripleLowCrossing
