module

public import PaperP1.Analysis.JointLargeFrequencyReduction
public import PaperP1.Analysis.FixedPowerJointRectangle
public import PaperP1.Analysis.OffCentralJointEnergy


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UniformRealOffCentralEnergy
open Finset Filter MeasureTheory PaperP1
open scoped Classical

def region (T T₀ : ℝ) : Set ℝ := Set.Ioc (-T) T ∩ {t : ℝ | T₀ ≤ |t|}

theorem region_measurable (T T₀ : ℝ) : MeasurableSet (region T T₀) :=
  measurableSet_Ioc.inter (isClosed_le continuous_const continuous_abs).measurableSet

theorem restricted_reduction (N : ℕ) (f : ℕ → ℂ) (T T₀ : ℝ) :
    (∫ t in region T T₀, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) ≤
      (∫ t in SmallPrimeRegion.goodSet (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) f T
        (FirstBandSmallRegion.threshold N), ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2)+
      (∫ t in ActualIntermediateFrequencyRegion.region N f T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2)+
      (∫ t in FixedPowerJointRectangle.region N f T T₀, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) := by
  let G := SmallPrimeRegion.goodSet (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) f T (FirstBandSmallRegion.threshold N)
  let I := ActualIntermediateFrequencyRegion.region N f T
  let J := FixedPowerJointRectangle.region N f T T₀
  let g := fun t ↦ ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2
  have hg : Continuous g := (GaussianExponentialSums.polynomial_continuous _ _ _).norm.pow 2
  have hG : G ⊆ Set.Ioc (-T) T := fun _ ht ↦ ht.1
  have hI : I ⊆ Set.Ioc (-T) T := fun _ ht ↦ ht.1
  have hJ : J ⊆ Set.Ioc (-T) T := fun t ht ↦ ((JointLargeFrequencyReduction.largeRegion_iff N f T t).mp ht.1).1
  have hGI : G ∪ I ⊆ Set.Ioc (-T) T := fun _ ht ↦ ht.elim (fun hg ↦ hG hg) (fun hi ↦ hI hi)
  have hCover : region T T₀ ⊆ (G ∪ I) ∪ J := by
    intro t ht
    by_cases hGI : t ∈ G ∪ I
    · exact Or.inl hGI
    · exact Or.inr ⟨⟨ht.1,hGI⟩,ht.2⟩
  have hDisjoint : Disjoint (G ∪ I) J := by
    apply Set.disjoint_left.mpr
    intro t htGI htJ
    exact htJ.1.2 htGI
  have hi : IntegrableOn g (Set.Ioc (-T) T) := (hg.intervalIntegrable (-T) T).1
  have hiGI : IntegrableOn g (G ∪ I) := hi.mono_set hGI
  have hiJ : IntegrableOn g J := hi.mono_set hJ
  have hiUnion : IntegrableOn g ((G ∪ I) ∪ J) :=
    hi.mono_set (fun _ ht ↦ ht.elim (fun hgi ↦ hGI hgi) (fun hj ↦ hJ hj))
  have hUnion : (∫ t in (G ∪ I) ∪ J, g t)=(∫ t in G, g t)+(∫ t in I, g t)+(∫ t in J, g t) := by
    rw [setIntegral_union hDisjoint (FixedPowerJointRectangle.region_measurable N f T T₀) hiGI hiJ,
      setIntegral_union (JointLargeFrequencyReduction.first_intermediate_disjoint N f T)
        (ActualIntermediateFrequencyRegion.region_measurable N f T) (hi.mono_set hG) (hi.mono_set hI)]
  have hMono := setIntegral_mono_set (μ := volume) hiUnion (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
    (Filter.Eventually.of_forall hCover)
  rw [hUnion] at hMono
  exact hMono

theorem uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ T : ℝ, 1 ≤ T →
      T ≤ (N : ℝ)/Real.log (N : ℝ) →
      (∫ t in region T T₀, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun n ↦ (f n : ℂ)) t‖^2) ≤ ε := by
  obtain ⟨NG,hNG,hGood⟩ := GrowingGoodFullPolynomial.first_good_part_small_uniform (ε/3) (by positivity)
  obtain ⟨NI,hNI,hIntermediate⟩ := IntermediateContributionSmall.full_small_uniform (ε/3) (by positivity)
  obtain ⟨T₀,hT₀,NJ,hNJ,hJoint⟩ := OffCentralJointEnergy.uniform_bound (ε/3) (by positivity)
  have hLogLimit := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NL,hLog⟩ := eventually_atTop.mp (hLogLimit.eventually (eventually_ge_atTop 1))
  refine ⟨T₀,hT₀,max 2 (max NG (max NI (max NJ NL))),by omega,?_⟩
  intro N hN f hf T hT hTime
  have hTP : 0 < T := by linarith only [hT]
  have hLog1 : 1 ≤ Real.log (N : ℝ) := hLog N (by omega)
  have hTN : T ≤ (N : ℝ) := hTime.trans (div_le_self (Nat.cast_nonneg N) hLog1)
  let fC : ℕ → ℂ := fun n ↦ (f n : ℂ)
  have hfC : ∀ n, 0 < n → ‖fC n‖ ≤ 1 := by
    intro n hn
    simpa only [fC,Complex.norm_real,Real.norm_eq_abs] using
      FinitePrimeDirichletTruncation.real_hom_bound f hf n (Nat.ne_of_gt hn)
  have hMultiply : ∀ m n, fC (m*n)=fC m*fC n := by
    intro m n
    dsimp only [fC]
    rw [map_mul,Complex.ofReal_mul]
  have hGoodBound := hGood N (by omega) fC hMultiply hfC T hTP hTime
  have hIntermediateBound := hIntermediate N (by omega) fC hMultiply hfC T hTP hTime
  have hJointBound := hJoint N (by omega) f hf T hT hTN
  have hReduction := restricted_reduction N fC T T₀
  dsimp only [fC] at hGoodBound hIntermediateBound hReduction
  linarith only [hReduction,hGoodBound,hIntermediateBound,hJointBound]
end PaperP1.UniformRealOffCentralEnergy
