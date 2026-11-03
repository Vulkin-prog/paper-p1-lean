module

public import PaperP1.Model.RetainedIndependentDeficitComparison
public import PaperP1.Asymptotics.HomogeneousChannelMass
public import PaperP1.Asymptotics.LogarithmicWordPowers

/-! # The actual retained good-pair joint mass has a uniform two-thirds power bound at every real private-prime threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedGoodPairMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RetainedReferenceTheorem
  PaperP1.HomogeneousRunMass PaperP1.HomogeneousChannelMass

theorem beta_le_raw {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    beta H N L ≤ PrimitiveNominalMass.mass (rawPrincipal N 0 L) L := by
  have hsub := RetainedIndependentDeficitComparison.good_subset_zero_channels (L := L) hN H
  calc
    _ ≤ ∑ e ∈ GoodEdgeCompression.goodEdges H N L, probability L e :=
      sum_le_sum (fun e _ ↦ actual_joint_le L hL e)
    _ ≤ ∑ e ∈ rawPrincipal N 0 L, probability L e :=
      sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ ↦ (probability_pos L e).le)
    _ = _ := sum_congr rfl (fun e he ↦ regular_weight (raw_principal_regular hN he))

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      beta H N L ≤ (N : ℝ) ^ (-2 / 3 + ε) := by
  obtain ⟨K, hK, NM, _hNM, hm⟩ := uniform_principal_upper C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    CriticalBandScale.upperScale CriticalBandScale.upperScale_pos.le K 1 ε hε
  refine ⟨3 + NM + NG + NP, by omega, ?_⟩
  intro N hN L hband H
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hwidth := (hg N (by omega) L hband).2.2.2.2.2
  have hcoef : K * L ≤ (N : ℝ) ^ ε := by
    calc
      _ ≤ K * ((L + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ L) hK.le
      _ ≤ |K * ((L + 1 : ℕ) : ℝ) ^ 1| := by rw [pow_one]; exact le_abs_self _
      _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using hp N (by omega) L hwidth
  calc
    _ ≤ PrimitiveNominalMass.mass (rawPrincipal N 0 L) L := beta_le_raw (by omega) hL H
    _ ≤ (K * L) * (N : ℝ) ^ (-2 / 3 : ℝ) := hm N (by omega) L 0 hband
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (-2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.RetainedGoodPairMass
