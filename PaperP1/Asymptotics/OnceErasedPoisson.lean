module

public import PaperP1.Model.OnceErasedCount
public import PaperP1.Asymptotics.ErasedPoissonCount

/-! # The once-erased count has Poisson approximation at its own actual mean -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OnceErasedPoisson

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw PaperP1.PositionalCountProjection
  PaperP1.PositionalDeletedFields PaperP1.ErasedCountReference PaperP1.AtomicProbability
  PaperP1.CriticalPairNegligible PaperP1.ErasedPoissonCount

theorem uniform_mean_error (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
        |OnceErasedCount.countMean H N L - singleMean H N L| ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := OriginalDeletedIntensity.uniform_bound C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband H
  have hh := h N hN L hband H
  have hsecond : 0 ≤ ∑ x ∈ dyadicBlock N, |PositionalFactorialCovariance.mean
      (isolatedLaw (GoodEdgeCompression.goodEdges H N L) (dyadicBlock N) L) x -
        ((2 ^ L : ℝ)⁻¹ - PositionalCompoundPoisson.incidence
          (GoodEdgeCompression.goodEdges H N L) (infiniteJointMoment L) x)| :=
    sum_nonneg (fun _ _ ↦ abs_nonneg _)
  rw [OnceErasedCount.countMean_eq_sum, singleMean_eq_sum (by omega : 2 ≤ N) H, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  linarith only [hh, hsecond]

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        OnceErasedCount.poissonDistance N L ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NF, _hNF, hf⟩ := PositionalOriginalDeletion.uniform_norm_bound C (ε / 2) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := uniform_mean_error C (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := ErasedCountMean.uniform_positive C
  obtain ⟨NC, hc⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NP + NC + NF + NM, by omega, ?_⟩
  intro N hN L hband
  let G := dyadicBlock N
  let H : ℝ := (8 * (L + 1) : ℕ)
  let E := GoodEdgeCompression.goodEdges H N L
  let t := fun x ↦ (2 ^ L : ℝ)⁻¹ - PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x
  let U := PositionalBernoulliProducts.poisson G t
  let ν := onceLaw E G L
  let s := singleMean H N L
  let m := OnceErasedCount.countMean H N L
  let P := OnceErasedCount.law H N L
  let R := (N : ℝ) ^ (-4 / 5 + ε / 2)
  have hs : 0 < s := hp N (by omega) L hband H
  let Q := WeightedPoissonNorm.poisson s hs.le
  have hsSum : (∑ x ∈ G, t x) = s := (singleMean_eq_sum (by omega : 2 ≤ N) H).symm
  have hproj : projection U = CompletedPoisson.poisson s :=
    (PositionalScalarDistance.poisson_projection G t).trans (congrArg CompletedPoisson.poisson hsSum)
  have hP (k : ℕ) : realMass P k = CompletedLaw.coeff k (projection ν) := OnceErasedCount.realMass_law H N L k
  have hQ (k : ℕ) : realMass Q k = CompletedLaw.coeff k (projection U) := by
    rw [hproj, CompletedPoisson.coeff_poisson]
    exact WeightedPoissonNorm.realMass_poisson s hs.le k
  have hscalar := PositionalScalarDistance.bound ν U P Q hP hQ
  have hfieldBound : ‖ν - U‖ ≤ R := (hf N (by omega) L hband).1
  have hPQ : totalVariation P Q ≤ R := by
    have hn := norm_nonneg (ν - U)
    linarith only [hscalar, hfieldBound, hn]
  have hparam : totalVariation Q (WeightedPoissonNorm.poisson m (OnceErasedCount.countMean_nonneg H N L)) ≤
      (N : ℝ) ^ (-1 + ε / 2) := by
    have hh := CompletedPoissonMetric.parameter_stability s m hs.le (OnceErasedCount.countMean_nonneg H N L)
    rw [← poisson_law_eq, ← poisson_law_eq] at hh
    apply hh.trans
    rw [abs_sub_comm]
    exact hm N (by omega) L hband H
  have hpower : (N : ℝ) ^ (-1 + ε / 2) ≤ R :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [])
  have hfactor : 2 * R ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    convert hc N (by omega) using 1
    congr 1
    ring
  have htri := AtomicProbabilityMetric.triangle P Q (WeightedPoissonNorm.poisson m (OnceErasedCount.countMean_nonneg H N L))
  change totalVariation P (WeightedPoissonNorm.poisson m (OnceErasedCount.countMean_nonneg H N L)) ≤ _
  linarith only [htri, hPQ, hparam.trans hpower, hfactor]

theorem uniform_relative (C : ℝ) :
    Negligible C OnceErasedCount.poissonDistance := by
  obtain ⟨N₀, _hN₀, h⟩ := uniform_bound C (1 / 30) (by norm_num)
  apply of_power_bound C (23 / 30) (by norm_num)
  refine ⟨N₀, ?_⟩
  intro N hN L hband
  rw [abs_of_nonneg (OnceErasedCount.poissonDistance_nonneg N L)]
  simpa only [show (-4 / 5 + 1 / 30 : ℝ) = -(23 / 30) by norm_num] using h N hN L hband


end PaperP1.OnceErasedPoisson
