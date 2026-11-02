module

public import PaperP1.Model.PairActivityHostCap
public import PaperP1.Asymptotics.JointFamilyProbabilityUnderBCN
public import PaperP1.Asymptotics.HeterogeneousRunConversion

/-! # A coarse vanishing bound for actual pair activity under the same BCN input

These rates are weaker than the manuscript's channel-sensitive rates.
They retain the actual marginals, all covariance signs and arbitrary subsets.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairActivityUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PairActivityHostCap
  PaperP1.HeterogeneousRunConversion PaperP1.CountObservables

theorem uniform_pair_activity (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      absoluteMass G L ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NH, hNH, hhosts⟩ := OriginalPairHosts.uniform_count C η hη
  obtain ⟨NP, hpairs⟩ := JointFamilyProbabilityUnderBCN.uniform_pair_probability c κ hc hBCN C η hη
  obtain ⟨NI, hind⟩ := PairHostIndependentMass.uniform_mass C η hη
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max NH (max NP (max NI NG)), by omega, ?_⟩
  intro N hN L hband G hG
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hfinite := finite_bound hNtwo hL (Real.rpow_nonneg hn.le (-3 / 2 + η))
    (fun x hx y hy hxy ↦ hpairs N (by omega) L x y hband hx hy hxy)
  have hproduct : ((PairHostCover.hosts N L).card : ℝ) * (N : ℝ) ^ (-3 / 2 + η) ≤
      (N : ℝ) ^ (-1 / 2 + ε) := by
    calc
      _ ≤ (N : ℝ) ^ (1 + η) * (N : ℝ) ^ (-3 / 2 + η) :=
        mul_le_mul_of_nonneg_right (hhosts N (by omega) L hband) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; dsimp [η]; ring
  have hi : PairHostIndependentMass.mass N L ≤ (N : ℝ) ^ (-1 / 2 + ε) :=
    (hind N (by omega) L hband).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [η]; linarith))
  exact (absoluteMass_mono hG L).trans (by linarith only [hfinite, hproduct, hi])

theorem uniform_conversion (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑' k : ℕ, |(FiniteLawEmbedding.embed (reference G L) -
        QuadraticPoisson.reference (countMoment G L 1)
          (RegularCumulantTransfer.secondFactorialCumulant G L)) {k}|) ≤
        (N : ℝ) ^ (-3 / 2 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let K := HeterogeneousRunConversionAsymptotic.errorConstant C
  have hK : 0 < K := HeterogeneousRunConversionAsymptotic.errorConstant_pos C
  obtain ⟨NA, hNA, hactivity⟩ := uniform_pair_activity c κ hc hBCN C η hη
  obtain ⟨NE, hNE, herror⟩ := HeterogeneousRunConversionAsymptotic.uniform_actual_bound C
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (2 * K) (-3 / 2 + η) η hη
  refine ⟨max NA (max NE NF), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsquare : 1 / (N : ℝ) ^ 2 ≤ (N : ℝ) ^ (-3 / 2 + η) := by
    rw [one_div, ← Real.rpow_two, ← Real.rpow_neg hn.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hpair : absoluteMass G L / N ≤ (N : ℝ) ^ (-3 / 2 + η) := by
    calc
      _ ≤ (N : ℝ) ^ (-1 / 2 + η) / N :=
        div_le_div_of_nonneg_right (hactivity N (by omega) L hband G hG) hn.le
      _ = _ := by
        rw [show (-3 / 2 + η) = (-1 / 2 + η) - 1 by ring,
          Real.rpow_sub hn, Real.rpow_one]
  calc
    _ ≤ K * (1 / (N : ℝ) ^ 2 + absoluteMass G L / N) := herror N (by omega) L hband G hG
    _ ≤ K * ((N : ℝ) ^ (-3 / 2 + η) + (N : ℝ) ^ (-3 / 2 + η)) :=
      mul_le_mul_of_nonneg_left (add_le_add hsquare hpair) hK.le
    _ = (2 * K) * (N : ℝ) ^ (-3 / 2 + η) := by ring
    _ ≤ (N : ℝ) ^ ((-3 / 2 + η) + η) := hfactor N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

end PaperP1.PairActivityUnderBCN
