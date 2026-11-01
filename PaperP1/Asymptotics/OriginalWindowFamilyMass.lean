module

public import PaperP1.Asymptotics.OriginalWindowFamilyCounts
public import PaperP1.Model.FamilyIndependentMass
public import PaperP1.Model.LocalRigidityConsequences

/-! # Main 10.2: actual connected and primitive original-window independent mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalWindowFamilyMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.FamilyIndependentMass

theorem uniform_marginals (Cband : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L x : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband → x ∈ dyadicBlock N →
      0 ≤ infiniteMarginal x L ∧ infiniteMarginal x L ≤ K / N := by
  obtain ⟨K, hK, NM, hNM⟩ := PaperP1.LocalRigidityConsequences.critical_band_marginals
    (1 / 2) Cband (by norm_num)
  obtain ⟨NG, hNG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry Cband 0
  refine ⟨K, hK, max NM NG, ?_⟩
  intro N hN L x hband hx
  obtain ⟨hNtwo, _, hBtwo, _, _, _⟩ := hNG N (by omega) L hband
  have hL : 0 < L := by omega
  have hNx := (mem_Ico.mp hx).1
  have hbaseNat : N ≤ 2 * (x - 1) := by omega
  have hbaseReal : (N : ℝ) ≤ 2 * (x - 1 : ℕ) := by exact_mod_cast hbaseNat
  have hbase : (1 / 2 : ℝ) * N ≤ (x - 1 : ℕ) := by linarith only [hbaseReal]
  refine ⟨PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L, ?_⟩
  by_cases hp : 0 < infiniteMarginal x L
  · exact (hNM N (by omega) x L hL hbase hband hp).2.2
  · exact (le_of_not_gt hp).trans (div_nonneg hK.le (Nat.cast_nonneg N))

theorem article_10_2 (r : ℕ) (hr : 2 ≤ r) (Cband ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband → G ⊆ dyadicBlock N →
      ((connectedFamilies G L r).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε) ∧
      ((primitiveFamilies G L r).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε) ∧
      independentMass (connectedFamilies G L r) L ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε) ∧
      independentMass (primitiveFamilies G L r) L ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε) := by
  classical
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NC, hNC⟩ := PaperP1.OriginalWindowFamilyCounts.uniform_hosts r hr Cband η hη
  obtain ⟨K, hK, NM, hNM⟩ := uniform_marginals Cband
  obtain ⟨NF, hNF⟩ := PaperP1.HalfCountSchedule.factor_absorption (K ^ r) (-(r : ℝ) / 2 + η) η hη
  refine ⟨max 2 (max NC (max NM NF)), ?_⟩
  intro N hN L G hband hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨hc, hp⟩ := hNC N (by omega) L G hband hG
  have hcap : ∀ x ∈ G, infiniteMarginal x L ≤ K / N := fun x hx ↦ (hNM N (by omega) L x hband (hG hx)).2
  have hmass : ∀ F : Finset (Finset ℕ), (∀ I ∈ F, I ⊆ G ∧ I.card = r) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + η) →
      independentMass F L ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε) := by
    intro F hF hcount
    have hproduct : (N : ℝ) ^ ((r : ℝ) / 2 + η) * (K / N) ^ r =
        K ^ r * (N : ℝ) ^ (-(r : ℝ) / 2 + η) := by
      calc
        _ = K ^ r * ((N : ℝ) ^ ((r : ℝ) / 2 + η) / (N : ℝ) ^ r) := by rw [div_pow]; ring
        _ = K ^ r * (N : ℝ) ^ (((r : ℝ) / 2 + η) - r) := by rw [Real.rpow_sub hn, Real.rpow_natCast]
        _ = _ := by rw [show ((r : ℝ) / 2 + η) - r = -(r : ℝ) / 2 + η by ring]
    calc
      _ ≤ (F.card : ℝ) * (K / N) ^ r := finite_mass_cap F G L r (K / N) hF hcap
      _ ≤ (N : ℝ) ^ ((r : ℝ) / 2 + η) * (K / N) ^ r :=
        mul_le_mul_of_nonneg_right hcount (pow_nonneg (div_nonneg hK.le hn.le) _)
      _ = K ^ r * (N : ℝ) ^ (-(r : ℝ) / 2 + η) := hproduct
      _ ≤ (N : ℝ) ^ ((-(r : ℝ) / 2 + η) + η) := hNF N (by omega)
      _ = _ := by congr 1; dsimp [η]; ring
  have hpower : (N : ℝ) ^ ((r : ℝ) / 2 + η) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [η]; linarith)
  refine ⟨hc.trans hpower, hp.trans hpower, hmass _ ?_ hc, hmass _ ?_ hp⟩
  · intro I hI
    exact mem_powersetCard.mp (mem_filter.mp hI).1
  · intro I hI
    exact mem_powersetCard.mp (mem_filter.mp hI).1

end PaperP1.OriginalWindowFamilyMass
