module

public import PaperP1.Analysis.ActualIntermediateFrequencyRegion
public import PaperP1.Analysis.GrowingGoodFullPolynomial
public import PaperP1.Analysis.IntermediateContributionSmall

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.JointLargeFrequencyReduction
open Finset Filter PaperP1 MeasureTheory
open scoped Classical

def largeRegion (N : ℕ) (f : ℕ → ℂ) (T : ℝ) : Set ℝ :=
  Set.Ioc (-T) T \ (SmallPrimeRegion.goodSet (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) f T
    (FirstBandSmallRegion.threshold N) ∪ ActualIntermediateFrequencyRegion.region N f T)

theorem largeRegion_measurable (N : ℕ) (f : ℕ → ℂ) (T : ℝ) : MeasurableSet (largeRegion N f T) :=
  measurableSet_Ioc.diff ((SmallPrimeRegion.goodSet_measurable _ _ _ _ _).union
    (ActualIntermediateFrequencyRegion.region_measurable N f T))

theorem largeRegion_iff (N : ℕ) (f : ℕ → ℂ) (T t : ℝ) :
    t ∈ largeRegion N f T ↔ t ∈ Set.Ioc (-T) T ∧
    (∃ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N),
      FirstBandSmallRegion.threshold N <
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) j) f t‖) ∧
    (∃ l ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N),
      (NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) l)^(-1/40 : ℝ) <
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N) l) f t‖) := by
  constructor
  · intro ht
    have hfirst : ¬∀ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N),
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) j) f t‖ ≤
          FirstBandSmallRegion.threshold N := by
      intro hall
      exact ht.2 (Or.inl ⟨ht.1,hall⟩)
    push Not at hfirst
    have hsecond : ¬∀ l ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N),
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N) l) f t‖ ≤
          (NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) l)^(-1/40 : ℝ) := by
      intro hall
      exact ht.2 (Or.inr ⟨ht.1,hfirst,hall⟩)
    push Not at hsecond
    exact ⟨ht.1,hfirst,hsecond⟩
  · rintro ⟨ht,⟨j,hj,hbig⟩,⟨l,hl,hlarge⟩⟩
    refine ⟨ht,?_⟩
    rintro (hg | hi)
    · exact (not_lt_of_ge (hg.2 j hj)) hbig
    · exact (not_lt_of_ge (hi.2.2 l hl)) hlarge

theorem first_intermediate_disjoint (N : ℕ) (f : ℕ → ℂ) (T : ℝ) :
    Disjoint (SmallPrimeRegion.goodSet (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) f T
      (FirstBandSmallRegion.threshold N)) (ActualIntermediateFrequencyRegion.region N f T) := by
  apply Set.disjoint_left.mpr
  intro t hg hi
  obtain ⟨j,hj,hbig⟩ := hi.2.1
  exact (not_lt_of_ge (hg.2 j hj)) hbig

theorem energy_split (N : ℕ) (f : ℕ → ℂ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2)=
      (∫ t in SmallPrimeRegion.goodSet (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) f T
        (FirstBandSmallRegion.threshold N), ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2)+
      (∫ t in ActualIntermediateFrequencyRegion.region N f T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2)+
      (∫ t in largeRegion N f T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) := by
  let G := SmallPrimeRegion.goodSet (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N) f T (FirstBandSmallRegion.threshold N)
  let I := ActualIntermediateFrequencyRegion.region N f T
  let B := largeRegion N f T
  let g := fun t ↦ ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2
  have hg : Continuous g := (GaussianExponentialSums.polynomial_continuous _ _ _).norm.pow 2
  have hGI : G ∪ I ⊆ Set.Ioc (-T) T := by
    intro t ht
    rcases ht with ht | ht
    · exact ht.1
    · exact ht.1
  have hUnion : (G ∪ I) ∪ B=Set.Ioc (-T) T := by
    ext t
    constructor
    · rintro (ht | ht)
      · exact hGI ht
      · exact ht.1
    · intro ht
      by_cases hh : t ∈ G ∪ I
      · exact Or.inl hh
      · exact Or.inr ⟨ht,hh⟩
  have hd : Disjoint (G ∪ I) B := by
    apply Set.disjoint_left.mpr
    intro t ht hb
    exact hb.2 ht
  have hi : IntegrableOn g (Set.Ioc (-T) T) := (hg.intervalIntegrable (-T) T).1
  have hiG : IntegrableOn g G := hi.mono_set (fun _t ht ↦ ht.1)
  have hiI : IntegrableOn g I := hi.mono_set (fun _t ht ↦ ht.1)
  have hiB : IntegrableOn g B := hi.mono_set (fun _t ht ↦ ht.1)
  calc
    _ = ∫ t in Set.Ioc (-T) T, g t := intervalIntegral.integral_of_le (by linarith : -T ≤ T)
    _ = ∫ t in (G ∪ I) ∪ B, g t := by rw [hUnion]
    _ = (∫ t in G ∪ I, g t)+(∫ t in B, g t) :=
      setIntegral_union hd (largeRegion_measurable N f T) (hi.mono_set hGI) hiB
    _ = _ := by
      rw [setIntegral_union (first_intermediate_disjoint N f T) (ActualIntermediateFrequencyRegion.region_measurable N f T) hiG hiI]

theorem reduction_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ a b, f (a*b)=f a*f b) → (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ (N : ℝ)/Real.log (N : ℝ) →
      (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) ≤
        ε+(∫ t in largeRegion N f T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) := by
  obtain ⟨N₁,hN₁,hGood⟩ := GrowingGoodFullPolynomial.first_good_part_small_uniform (ε/2) (by positivity)
  obtain ⟨N₂,hN₂,hInter⟩ := IntermediateContributionSmall.full_small_uniform (ε/2) (by positivity)
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN f hf hb T hT hTN
  have h1 := hGood N (by omega) f hf hb T hT hTN
  have h2 := hInter N (by omega) f hf hb T hT hTN
  have hs := energy_split N f T hT.le
  linarith only [hs,h1,h2]
end PaperP1.JointLargeFrequencyReduction
