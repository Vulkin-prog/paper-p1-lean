module

public import PaperP1.Asymptotics.CoarseDependentFamilyMassUnderBCN
public import PaperP1.Model.DependentFactorialBound
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Model.RegularMomentTransfer

/-! # Uniform bounds for every fixed actual count moment under explicit BCN

Dependent-family propagation gives a factorial upper bound using the exact
heterogeneous mean. This discharges the higher-moment premise of the proved
regular-count transfer theorem. The fixed-moment correction and sharp remainder
of main Theorem 6.4 remain separate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedCountMomentBoundsUnderBCN

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HeterogeneousDirectMaximum
  PaperP1.CountObservables PaperP1.FactorialCountMoments PaperP1.DependentFamilySeeds

theorem uniform_factorial_upper (r : ℕ) (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      factorialCountMoment G L r ≤ actualMean G L ^ r + (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨ND, _hND, hmass⟩ := CoarseDependentFamilyMassUnderBCN.uniform_dependent_mass r c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (r.factorial : ℝ) (-1 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max ND (max NG NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hd : (r.factorial : ℝ) * dependentMass G L r ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
    calc
      _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ (-1 / 2 + ε / 2) :=
        mul_le_mul_of_nonneg_left (hmass N (by omega) L hband G hG) (Nat.cast_nonneg _)
      _ ≤ (N : ℝ) ^ ((-1 / 2 + ε / 2) + ε / 2) := hfactor N (by omega)
      _ = _ := by congr 1; ring
  exact (DependentFactorialBound.factorial_upper hG hL r).trans (add_le_add le_rfl hd)

theorem uniform_factorial_bound (r : ℕ) (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      factorialCountMoment G L r ≤ B := by
  obtain ⟨NF, _hNF, hfac⟩ := uniform_factorial_upper r c κ hc hBCN C (1 / 4) (by norm_num)
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  let M : ℝ := 2 * (2 : ℝ) ^ C
  refine ⟨M ^ r + 1, by dsimp [M]; positivity, max NF NM, by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hm : actualMean G L ≤ M := by
    calc
      _ ≤ actualMean (dyadicBlock N) L :=
        sum_le_sum_of_subset_of_nonneg hG (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
      _ = countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment (subset_refl _)
      _ ≤ _ := (hmean N (by omega) L hband).2
  have hμ : 0 ≤ actualMean G L := sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have he : (N : ℝ) ^ (-1 / 2 + (1 / 4 : ℝ)) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-1 / 2 : ℝ) + 1 / 4 ≤ 0)
  exact (hfac N (by omega) L hband G hG).trans (add_le_add (pow_le_pow_left₀ hμ hm r) he)

theorem uniform_ordinary_bound (r : ℕ) (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      countMoment G L r ≤ B := by
  obtain ⟨B, hB, N₀, hN₀, hbound⟩ := uniform_factorial_bound r c κ hc hBCN C
  refine ⟨(((2 * r) ^ r : ℕ) : ℝ) + 2 ^ r * B, by positivity, N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  exact (DependentFactorialBound.ordinary_upper hG r).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hbound N hN L hband G hG) (by positivity)))

theorem uniformlyBoundedCountMoments (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ) :
    RegularMomentTransfer.UniformlyBoundedCountMoments C := by
  intro q _hq
  obtain ⟨B, hB, N₀, _hN₀, hbound⟩ := uniform_ordinary_bound q c κ hc hBCN C
  refine ⟨B, hB, N₀, ?_⟩
  intro N hN L _hallowed _hL hband
  exact hbound N hN L hband (dyadicBlock N) (subset_refl _)

theorem regular_moment_transfer (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C : ℝ)
    (j : ℕ) (hj : 0 < j) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |countMoment (dyadicBlock N) L j - countMoment (RegularStarts.regularStarts N L) L j| ≤
        K * (N : ℝ) ^ (-1 + ε) :=
  RegularMomentTransfer.regular_moment_transfer C (uniformlyBoundedCountMoments c κ hc hBCN C) j hj ε hε

end PaperP1.FixedCountMomentBoundsUnderBCN
