module

public import PaperP1.Analysis.FinitePrimeDirichletTruncation
public import PaperP1.Analysis.TwoBandRectangleApproximation
public import PaperP1.Analysis.FixedPowerLargeIntegral
public import PaperP1.Analysis.FixedPowerSmallIntegral


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedPowerJointRectangle
open Finset Filter MeasureTheory PaperP1
open scoped Classical

def region (N : ℕ) (f : ℕ → ℂ) (T T₀ : ℝ) : Set ℝ :=
  JointLargeFrequencyReduction.largeRegion N f T ∩ {t : ℝ | T₀ ≤ |t|}

theorem region_measurable (N : ℕ) (f : ℕ → ℂ) (T T₀ : ℝ) : MeasurableSet (region N f T T₀) :=
  (JointLargeFrequencyReduction.largeRegion_measurable N f T).inter
    (isClosed_le continuous_const continuous_abs).measurableSet

theorem uniform_bound (a b : ℝ) (ha : 0 < a) (hb : b ≤ 1/16)
    (H : ℕ) (hH : 4 ≤ H) (hOrder : 2 ≤ a*(H : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) → ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      ∀ T : ℝ, 1 ≤ T → T ≤ (N : ℝ) →
      (∫ t in region N (fun n ↦ (f n : ℂ)) T T₀,
        ‖NarrowRamareRectangle.rectangle N H (FixedPowerPrimeBand.primes a b N) Q (fun n ↦ (f n : ℂ)) t‖^2) ≤ ε := by
  obtain ⟨T₀,hT₀,NL,hNL,hLarge⟩ := FixedPowerLargeIntegral.uniform_bound a b ha hb H hH hOrder (ε/2) (by positivity)
  obtain ⟨NS,hNS,hSmall⟩ := FixedPowerSmallIntegral.uniform_bound a b hb H hH (ε/2) (by positivity)
  refine ⟨T₀,hT₀,max NL NS,by omega,?_⟩
  intro N hN Q hQ f hf T hT hTN
  let fC : ℕ → ℂ := fun n ↦ (f n : ℂ)
  have hfC : ∀ n, 0 < n → ‖fC n‖ ≤ 1 := by
    intro n hn
    simpa only [fC,Complex.norm_real,Real.norm_eq_abs] using FinitePrimeDirichletTruncation.real_hom_bound f hf n (Nat.ne_of_gt hn)
  let D := region N fC T T₀
  let S := FixedPowerSmallIntegral.region a b H N fC T
  let L := FixedPowerLargeIntegral.region a b H N fC T T₀
  let g := fun t ↦ ‖NarrowRamareRectangle.rectangle N H (FixedPowerPrimeBand.primes a b N) Q fC t‖^2
  have hg : Continuous g := (TwoBandRectangleApproximation.rectangle_continuous _ _ _ _ _).norm.pow 2
  have hS : S ⊆ Set.Ioc (-T) T := fun t ht ↦ ((JointLargeFrequencyReduction.largeRegion_iff N fC T t).mp ht.1).1
  have hL : L ⊆ Set.Ioc (-T) T := fun _ ht ↦ ht.1.1
  have hCover : D ⊆ S ∪ L := by
    intro t ht
    by_cases hGood : t ∈ SmallPrimeRegion.goodSet H (FixedPowerPrimeBand.primes a b N) fC T (1/(Real.log (N : ℝ))^100)
    · exact Or.inl ⟨ht.1,hGood⟩
    · exact Or.inr ⟨⟨((JointLargeFrequencyReduction.largeRegion_iff N fC T t).mp ht.1).1,hGood⟩,ht.2⟩
  have hDisjoint : Disjoint S L := by
    apply Set.disjoint_left.mpr
    intro t htS htL
    exact htL.1.2 htS.2
  have hi : IntegrableOn g (Set.Ioc (-T) T) := (hg.intervalIntegrable (-T) T).1
  have hiS : IntegrableOn g S := hi.mono_set hS
  have hiL : IntegrableOn g L := hi.mono_set hL
  have hiUnion : IntegrableOn g (S ∪ L) := hi.mono_set (fun _ ht ↦ ht.elim (fun hs ↦ hS hs) (fun hl ↦ hL hl))
  have hUnion : (∫ t in S ∪ L, g t)=(∫ t in S, g t)+(∫ t in L, g t) :=
    setIntegral_union hDisjoint (FixedPowerLargeIntegral.region_measurable a b H N fC T T₀) hiS hiL
  have hMono := setIntegral_mono_set (μ := volume) hiUnion (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
    (Filter.Eventually.of_forall hCover)
  rw [hUnion] at hMono
  have hSmallBound : (∫ t in S, g t) ≤ ε/2 := hSmall N (by omega) Q fC hfC T hT hTN
  have hLargeBound : (∫ t in L, g t) ≤ ε/2 := hLarge N (by omega) Q hQ f hf T (by linarith only [hT]) hTN
  exact hMono.trans (by linarith only [hSmallBound,hLargeBound])
end PaperP1.FixedPowerJointRectangle
