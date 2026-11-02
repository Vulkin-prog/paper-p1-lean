module

public import PaperP1.Probability.SeedProductBound
public import PaperP1.Model.DependentFamilySeeds
public import PaperP1.Asymptotics.OriginalWindowFamilyCounts
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Unconditional fixed-order product mass of geometrically dependent families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DependentProductMass

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.DependentFamilySeeds PaperP1.HeterogeneousDirectMaximum

def mass (G : Finset ℕ) (L r : ℕ) : ℝ :=
  ∑ I ∈ dependentFamilies G L r, ∏ x ∈ I, infiniteMarginal x L

def seededMass (G : Finset ℕ) (L r s : ℕ) : ℝ :=
  ∑ I ∈ seededFamilies G L r s, ∏ x ∈ I, infiniteMarginal x L

theorem cover_bound (G : Finset ℕ) (L r : ℕ) :
    mass G L r ≤ ∑ s ∈ Icc 2 r, seededMass G L r s := by
  have hp (I : Finset ℕ) : 0 ≤ ∏ x ∈ I, infiniteMarginal x L :=
    prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  exact (sum_le_sum_of_subset_of_nonneg (dependent_cover G L r) (fun I _ _ ↦ hp I)).trans
    (GraphStarWeights.sum_biUnion_le_nonneg (Icc 2 r) (seededFamilies G L r)
      (fun I ↦ ∏ x ∈ I, infiniteMarginal x L) hp)

theorem uniform_seeded_mass (s : ℕ) (hs : 2 ≤ s) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      seededMass G L (s + k) s ≤ (N : ℝ) ^ (-1 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let M : ℝ := 2 * (2 : ℝ) ^ C
  let D : ℝ := M ^ s * (M ^ k / (k.factorial : ℝ))
  obtain ⟨NC, hcount⟩ := OriginalWindowFamilyCounts.uniform_hosts s hs C η hη
  obtain ⟨NP, hcap⟩ := TripleRankGeometry.critical_nominal_marginal_cap C
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption D (-1 + η) η hη
  refine ⟨max 2 (max NC (max NP (max NM NF))), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp (x : ℕ) : 0 ≤ infiniteMarginal x L := MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmeanG : actualMean G L ≤ M := by
    calc
      _ ≤ actualMean (dyadicBlock N) L := sum_le_sum_of_subset_of_nonneg hG (fun x _ _ ↦ hp x)
      _ = CountObservables.countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment (subset_refl _)
      _ ≤ _ := (hmean N (by omega) L hband).2
  have hlocal (x : ℕ) (hx : x ∈ G) : infiniteMarginal x L ≤ M / N := by
    calc
      _ ≤ 2 * (2 ^ L : ℝ)⁻¹ := hcap N (by omega) L hband x (hG hx)
      _ ≤ 2 * ((2 : ℝ) ^ C / N) :=
        mul_le_mul_of_nonneg_left (LocalRigidityConsequences.nominal_marginal_bound (by omega) hband) (by norm_num)
      _ = _ := by dsimp [M]; ring
  have hseed : (∑ I ∈ primitiveFamilies G L s, ∏ x ∈ I, infiniteMarginal x L) ≤
      (N : ℝ) ^ ((s : ℝ) / 2 + η) * (M / N) ^ s := by
    calc
      _ ≤ ∑ _I ∈ primitiveFamilies G L s, (M / N) ^ s := by
        apply sum_le_sum
        intro I hI
        have hi := primitive_mem hI
        calc
          _ ≤ ∏ _x ∈ I, M / N := prod_le_prod₀ (fun x _ ↦ hp x) (fun x hx ↦ hlocal x (hi.1 hx))
          _ = _ := by rw [prod_const, hi.2]
      _ = ((primitiveFamilies G L s).card : ℝ) * (M / N) ^ s := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcount N (by omega) L G hband hG).2 (by positivity)
  have hraw := SeedProductBound.power_bound G (fun x ↦ infiniteMarginal x L) hp s k
    (primitiveFamilies G L s) (seededFamilies G L (s + k) s)
    (fun I hI ↦ primitive_mem hI) (fun I hI ↦ seeded_mem hI)
  have hcoeff : actualMean G L ^ k / (k.factorial : ℝ) ≤ M ^ k / (k.factorial : ℝ) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (sum_nonneg fun x _ ↦ hp x) hmeanG k) (Nat.cast_nonneg _)
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  calc
    _ ≤ (∑ I ∈ primitiveFamilies G L s, ∏ x ∈ I, infiniteMarginal x L) *
        (actualMean G L ^ k / (k.factorial : ℝ)) := hraw
    _ ≤ ((N : ℝ) ^ ((s : ℝ) / 2 + η) * (M / N) ^ s) * (M ^ k / (k.factorial : ℝ)) :=
      mul_le_mul hseed hcoeff
        (div_nonneg (pow_nonneg (sum_nonneg fun x _ ↦ hp x) k) (Nat.cast_nonneg _)) (by positivity)
    _ = D * ((N : ℝ) ^ ((s : ℝ) / 2 + η) / (N : ℝ) ^ s) := by dsimp [D]; rw [div_pow]; ring
    _ = D * (N : ℝ) ^ (((s : ℝ) / 2 + η) - s) := by rw [Real.rpow_sub hn, Real.rpow_natCast]
    _ ≤ D * (N : ℝ) ^ (-1 + η) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hsR])) (by dsimp [D]; positivity)
    _ ≤ (N : ℝ) ^ ((-1 + η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_seed_orders (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ s ∈ Icc 2 r, seededMass G L r s ≤ (N : ℝ) ^ (-1 + ε) := by
  have heach (s : ℕ) (hs : s ∈ Icc 2 r) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      seededMass G L r s ≤ (N : ℝ) ^ (-1 + ε) := by
    obtain ⟨NS, _hNS, hS⟩ := uniform_seeded_mass s (mem_Icc.mp hs).1 (r - s) C ε hε
    refine eventually_atTop.mpr ⟨NS, ?_⟩
    intro N hN L hband G hG
    have hsle := (mem_Icc.mp hs).2
    have hsr : s + (r - s) = r := by omega
    simpa only [hsr] using hS N hN L hband G hG
  obtain ⟨NF, hF⟩ := eventually_atTop.mp ((Finset.eventually_all (Icc 2 r)).mpr heach)
  refine ⟨max 2 NF, by omega, ?_⟩
  intro N hN L hband G hG s hs
  exact hF N (by omega) s hs L hband G hG

theorem uniform_mass (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      mass G L r ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NS, _hNS, hseed⟩ := uniform_seed_orders r C (ε / 2) (by positivity)
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption ((r + 1 : ℕ) : ℝ) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NS NF), by omega, ?_⟩
  intro N hN L hband G hG
  have hcard : ((Icc 2 r).card : ℝ) ≤ (r + 1 : ℕ) := by
    exact_mod_cast (show (Icc 2 r).card ≤ r + 1 by rw [Nat.card_Icc]; omega)
  calc
    _ ≤ ∑ s ∈ Icc 2 r, seededMass G L r s := cover_bound G L r
    _ ≤ ∑ _s ∈ Icc 2 r, (N : ℝ) ^ (-1 + ε / 2) := sum_le_sum (fun s hs ↦ hseed N (by omega) L hband G hG s hs)
    _ = ((Icc 2 r).card : ℝ) * (N : ℝ) ^ (-1 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((r + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-1 + ε / 2) := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hfactor N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.DependentProductMass
