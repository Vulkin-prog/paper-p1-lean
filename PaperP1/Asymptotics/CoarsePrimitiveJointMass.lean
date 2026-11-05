module

public import PaperP1.Model.PrimitiveActiveSeeds
public import PaperP1.Asymptotics.PrimitiveGeneralMass
public import PaperP1.Asymptotics.PairActivity

/-! # An unconditional vanishing joint mass at every fixed primitive order

Only the two-site branch previously used BCN. Its actual joint mass is now
bounded by the proved covariance activity and elementary independent weights.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarsePrimitiveJointMass

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.PrimitiveActiveSeeds PaperP1.HeterogeneousRunConversion

theorem finite_pair_bound (G : Finset ℕ) (L : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hcap : ∀ x ∈ G, infiniteMarginal x L ≤ M) :
    jointMass G L 2 ≤ absoluteMass G L + (primitiveFamilies G L 2).card * M ^ 2 := by
  classical
  let F := primitiveFamilies G L 2
  have hF : F ⊆ G.powersetCard 2 := filter_subset _ _
  have hpoint (I : Finset ℕ) (hI : I ∈ F) :
      infiniteJointMoment L I ≤ |infiniteCenteredCoefficient L I| + M ^ 2 := by
    obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp (hF hI)
    obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hcard
    have hid := CompressedJointMoments.centered_pair L {x, y} (card_pair hxy)
    rw [prod_pair hxy] at hid
    have hx := hcap x (hIG (mem_insert_self x {y}))
    have hy := hcap y (hIG (mem_insert_of_mem (mem_singleton_self y)))
    have hprod : infiniteMarginal x L * infiniteMarginal y L ≤ M ^ 2 := by
      simpa only [pow_two] using mul_le_mul hx hy (marginal_bounds y L).1 hM
    have hc := le_abs_self (infiniteCenteredCoefficient L {x, y})
    linarith only [hid, hc, hprod]
  have hc : (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ absoluteMass G L :=
    sum_le_sum_of_subset_of_nonneg hF (fun I _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L I))
  calc
    _ ≤ ∑ I ∈ F, (|infiniteCenteredCoefficient L I| + M ^ 2) := sum_le_sum hpoint
    _ = (∑ I ∈ F, |infiniteCenteredCoefficient L I|) + (F.card : ℝ) * M ^ 2 := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    _ ≤ _ := by linarith only [hc]

theorem uniform_pair_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      jointMass G L 2 ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NC, hcount⟩ := OriginalWindowFamilyCounts.uniform_hosts 2 (by decide) C η hη
  obtain ⟨NA, _hNA, ha⟩ := PairActivity.uniform_pair_activity C η hη
  obtain ⟨K, hK, NM, hm⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (1 + K ^ 2) (-1 / 2 + η) η hη
  refine ⟨2 + NC + NA + NM + NF, by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hcard := (hcount N (by omega) L G hband hG).2
  norm_num only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0)] at hcard
  have hfinite := finite_pair_bound G L (K / N) (by positivity)
    (fun x hx ↦ (hm N (by omega) L x hband (hG hx)).2)
  have hactivity : absoluteMass G L ≤ (N : ℝ) ^ (-1 / 2 + η) :=
    (ha N (by omega) L hband G hG).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  have hind : ((primitiveFamilies G L 2).card : ℝ) * (K / N) ^ 2 ≤
      K ^ 2 * (N : ℝ) ^ (-1 / 2 + η) := by
    calc
      _ ≤ (N : ℝ) ^ (1 + η) * (K / N) ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = K ^ 2 * (N : ℝ) ^ (-1 + η) := by
        rw [show -1 + η = (1 + η) - 2 by ring, Real.rpow_sub hn, Real.rpow_two, div_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
        (sq_nonneg K)
  calc
    _ ≤ absoluteMass G L + (primitiveFamilies G L 2).card * (K / N) ^ 2 := hfinite
    _ ≤ (1 + K ^ 2) * (N : ℝ) ^ (-1 / 2 + η) := by linarith only [hactivity, hind]
    _ ≤ (N : ℝ) ^ ((-1 / 2 + η) + η) := hf N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_mass (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      jointMass G L r ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  by_cases hr2 : r = 2
  · subst r
    exact uniform_pair_mass C ε hε
  · obtain ⟨NP, hprob⟩ := PrimitiveGeneralMass.actual_joint_submass r hr C ε hε
    refine ⟨max 2 NP, by omega, ?_⟩
    intro N hN L hband G hG
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hrR : (3 : ℝ) ≤ r := by exact_mod_cast (show 3 ≤ r by omega)
    exact (hprob N (by omega) L G (primitiveFamilies G L r) hband hG (subset_refl _)).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hrR]))

theorem uniform_finite_orders (K : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ r ∈ Icc 2 K, jointMass G L r ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  have heach (r : ℕ) (hr : r ∈ Icc 2 K) : ∀ᶠ N : ℕ in atTop, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      jointMass G L r ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
    obtain ⟨NR, _hNR, hR⟩ := uniform_mass r (mem_Icc.mp hr).1 C ε hε
    exact eventually_atTop.mpr ⟨NR, fun N hN ↦ hR N hN⟩
  obtain ⟨NF, hF⟩ := eventually_atTop.mp ((Finset.eventually_all (Icc 2 K)).mpr heach)
  refine ⟨max 2 NF, by omega, ?_⟩
  intro N hN L hband G hG r hr
  exact hF N (by omega) r hr L hband G hG

end PaperP1.CoarsePrimitiveJointMass
