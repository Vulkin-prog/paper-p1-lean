module

public import PaperP1.Asymptotics.UnorderedSeedMassPropagation
public import PaperP1.Asymptotics.CoarsePrimitiveJointMass
public import PaperP1.Model.DependentFamilySeeds
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Every fixed-order actual dependent joint mass vanishes without unproved inputs

This uses fixed-order seed propagation and a finite cover by minimal seeds.
It asserts no estimate uniform in an order growing with N.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseDependentFamilyMass

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.PrimitiveActiveSeeds PaperP1.DependentFamilySeeds

theorem uniform_seeded_mass (s : ℕ) (hs : 2 ≤ s) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      seededMass G L (s + k) s ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  let η := ε / 3
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NP, hprop⟩ := UnorderedSeedMassPropagation.uniform_mass s (by omega) k C η hη
  obtain ⟨NQ, _hNQ, hmass⟩ := CoarsePrimitiveJointMass.uniform_mass s hs C η hη
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption ((s + k).factorial : ℝ) (-1 / 2 + 2 * η) η hη
  refine ⟨max 2 (max NP (max NQ (max NG NF))), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hp := hprop N (by omega) L hL hband (primitiveFamilies G L s)
    (fun D hD ↦ ⟨(primitive_mem hD).1.trans hG, (primitive_mem hD).2⟩)
    (seededFamilies G L (s + k) s)
    (fun I hI ↦ ⟨(seeded_mem hI).1.trans hG, (seeded_mem hI).2⟩)
  calc
    _ ≤ ((s + k).factorial : ℝ) * (N : ℝ) ^ η * jointMass G L s := hp
    _ ≤ ((s + k).factorial : ℝ) * (N : ℝ) ^ η * (N : ℝ) ^ (-1 / 2 + η) :=
      mul_le_mul_of_nonneg_left (hmass N (by omega) L hband G hG) (by positivity)
    _ = ((s + k).factorial : ℝ) * (N : ℝ) ^ (-1 / 2 + 2 * η) := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 2
      ring
    _ ≤ (N : ℝ) ^ ((-1 / 2 + 2 * η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_seed_orders (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ s ∈ Icc 2 r, seededMass G L r s ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  have heach (s : ℕ) (hs : s ∈ Icc 2 r) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      seededMass G L r s ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
    obtain ⟨NS, _hNS, hS⟩ := uniform_seeded_mass s (mem_Icc.mp hs).1 (r - s) C ε hε
    apply eventually_atTop.mpr
    refine ⟨NS, ?_⟩
    intro N hN L hband G hG
    have hsle := (mem_Icc.mp hs).2
    have hsr : s + (r - s) = r := by omega
    simpa only [hsr] using hS N hN L hband G hG
  obtain ⟨NF, hF⟩ := eventually_atTop.mp ((Finset.eventually_all (Icc 2 r)).mpr heach)
  refine ⟨max 2 NF, by omega, ?_⟩
  intro N hN L hband G hG s hs
  exact hF N (by omega) s hs L hband G hG

theorem uniform_dependent_mass (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      dependentMass G L r ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨NS, _hNS, hseeds⟩ := uniform_seed_orders r C (ε / 2) (by positivity)
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption ((r + 1 : ℕ) : ℝ)
    (-1 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NS NF), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard : ((Icc 2 r).card : ℝ) ≤ (r + 1 : ℕ) := by
    exact_mod_cast (show (Icc 2 r).card ≤ r + 1 by rw [Nat.card_Icc]; omega)
  calc
    _ ≤ ∑ s ∈ Icc 2 r, seededMass G L r s := dependentMass_le_seeded G L r
    _ ≤ ∑ _s ∈ Icc 2 r, (N : ℝ) ^ (-1 / 2 + ε / 2) :=
      sum_le_sum (fun s hs ↦ hseeds N (by omega) L hband G hG s hs)
    _ = ((Icc 2 r).card : ℝ) * (N : ℝ) ^ (-1 / 2 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((r + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-1 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hn.le _)
    _ ≤ (N : ℝ) ^ ((-1 / 2 + ε / 2) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.CoarseDependentFamilyMass
