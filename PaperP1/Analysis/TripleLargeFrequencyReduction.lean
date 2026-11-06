module

public import PaperP1.Analysis.JointLargeFrequencyReduction
public import PaperP1.Analysis.FinalSmallPrimeSamples
public import PaperP1.Analysis.FinalSmallPrimeIntegral

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.TripleLargeFrequencyReduction
open Finset Filter MeasureTheory PaperP1
open scoped Classical

def largeRegion (B N : ℕ) (f : ℕ → ℂ) (T : ℝ) : Set ℝ :=
  JointLargeFrequencyReduction.largeRegion N f T \
    SmallPrimeRegion.goodSet (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N) f T
      (FinalSmallPrimeSamples.threshold N)

theorem largeRegion_measurable (B N : ℕ) (f : ℕ → ℂ) (T : ℝ) : MeasurableSet (largeRegion B N f T) :=
  (JointLargeFrequencyReduction.largeRegion_measurable N f T).diff
    (SmallPrimeRegion.goodSet_measurable _ _ f T _)

theorem largeRegion_iff (B N : ℕ) (f : ℕ → ℂ) (T t : ℝ) :
    t ∈ largeRegion B N f T ↔ t ∈ Set.Ioc (-T) T ∧
    (∃ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N),
      FirstBandSmallRegion.threshold N <
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) j) f t‖) ∧
    (∃ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N),
      (NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) j)^(-1/40 : ℝ) <
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N) j) f t‖) ∧
    (∃ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N),
      FinalSmallPrimeSamples.threshold N <
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N) j) f t‖) := by
  constructor
  · intro ht
    have hJ := (JointLargeFrequencyReduction.largeRegion_iff N f T t).mp ht.1
    have hNot : ¬∀ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N),
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (FinalPrimeBandGeometry.primes B N) j) f t‖ ≤
          FinalSmallPrimeSamples.threshold N := by
      intro hall
      exact ht.2 ⟨hJ.1,hall⟩
    push Not at hNot
    exact ⟨hJ.1,hJ.2.1,hJ.2.2,hNot⟩
  · rintro ⟨ht,hFirst,hSecond,hFinal⟩
    refine ⟨(JointLargeFrequencyReduction.largeRegion_iff N f T t).mpr ⟨ht,hFirst,hSecond⟩,?_⟩
    intro hGood
    obtain ⟨j,hj,hLarge⟩ := hFinal
    exact (not_lt_of_ge (hGood.2 j hj)) hLarge

theorem joint_energy_split (B N : ℕ) (f : ℕ → ℂ) (T : ℝ) :
    (∫ t in JointLargeFrequencyReduction.largeRegion N f T,
      ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2)=
    (∫ t in FinalSmallPrimeIntegral.region B N f T,
      ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2)+
    (∫ t in largeRegion B N f T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) := by
  let D := JointLargeFrequencyReduction.largeRegion N f T
  let E := FinalSmallPrimeIntegral.region B N f T
  let L := largeRegion B N f T
  let g := fun t ↦ ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2
  have hg : Continuous g := (GaussianExponentialSums.polynomial_continuous _ _ _).norm.pow 2
  have hD : D ⊆ Set.Ioc (-T) T := fun t ht ↦ (JointLargeFrequencyReduction.largeRegion_iff N f T t |>.mp ht).1
  have hUnion : E ∪ L=D := by
    ext t
    constructor
    · rintro (ht | ht)
      · exact ht.1
      · exact ht.1
    · intro ht
      by_cases hh : t ∈ SmallPrimeRegion.goodSet (GrowingFirstGoodRegion.width N)
          (FinalPrimeBandGeometry.primes B N) f T (FinalSmallPrimeSamples.threshold N)
      · exact Or.inl ⟨ht,hh⟩
      · exact Or.inr ⟨ht,hh⟩
  have hDisjoint : Disjoint E L := by
    apply Set.disjoint_left.mpr
    intro t ht hL
    exact hL.2 ht.2
  have hi : IntegrableOn g (Set.Ioc (-T) T) := (hg.intervalIntegrable (-T) T).1
  have hiE : IntegrableOn g E := hi.mono_set (fun _t ht ↦ hD ht.1)
  have hiL : IntegrableOn g L := hi.mono_set (fun _t ht ↦ hD ht.1)
  change (∫ t in D, g t)=(∫ t in E, g t)+(∫ t in L, g t)
  rw [← hUnion]
  exact setIntegral_union hDisjoint (largeRegion_measurable B N f T) hiE hiL

theorem energy_split (B N : ℕ) (f : ℕ → ℂ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2)=
      (∫ t in SmallPrimeRegion.goodSet (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) f T
        (FirstBandSmallRegion.threshold N), ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2)+
      (∫ t in ActualIntermediateFrequencyRegion.region N f T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2)+
      (∫ t in FinalSmallPrimeIntegral.region B N f T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2)+
      (∫ t in largeRegion B N f T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) := by
  have hh := JointLargeFrequencyReduction.energy_split N f T hT
  rw [joint_energy_split B N f T] at hh
  linarith only [hh]

theorem reduction_small_uniform (B : ℕ) (hB : 32 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ a b, f (a*b)=f a*f b) → (∀ n, 0 < n → ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 1 ≤ T → T ≤ (N : ℝ)/Real.log (N : ℝ) →
      (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) ≤
        ε+(∫ t in largeRegion B N f T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) := by
  obtain ⟨NO,hNO,hOld⟩ := JointLargeFrequencyReduction.reduction_small_uniform (ε/2) (by positivity)
  obtain ⟨NF,hNF,hFinal⟩ := FinalSmallPrimeIntegral.full_small_uniform B hB (ε/2) (by positivity)
  obtain ⟨NZ,hZ⟩ := eventually_atTop.mp (SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1))
  refine ⟨max NO (max NF NZ),by omega,?_⟩
  intro N hN f hf hb T hT hTN
  have hTp : 0 < T := by linarith only [hT]
  have hLog1 : 1 ≤ Real.log (N : ℝ) := hZ N (by omega)
  have hLog : 0 < Real.log (N : ℝ) := by linarith only [hLog1]
  have hTX : T ≤ N := hTN.trans ((div_le_iff₀ hLog).mpr (by
    have hNN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith only [hLog1,hNN]))
  have hOldBound := hOld N (by omega) f hf hb T hTp hTN
  have hFinalBound := hFinal N (by omega) f hf hb T hT hTX
  have hSplit := joint_energy_split B N f T
  linarith only [hOldBound,hFinalBound,hSplit]
end PaperP1.TripleLargeFrequencyReduction
