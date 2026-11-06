module

public import PaperP1.Analysis.UniformRealOffCentralEnergy
public import PaperP1.Analysis.GaussianDifferenceWeights
public import PaperP1.Analysis.GaussianDirichletTail


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GaussianEnergyReduction
open Finset MeasureTheory PaperP1 GaussianDirichletTail GaussianDifferenceWeights
open scoped Classical

theorem quantitative_bound (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (hS : S ⊆ Ico N (2*N))
    (a : ℕ → ℂ) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) (b c R T : ℝ)
    (hb : 0 < b) (hbc : b ≤ c) (hR : 0 ≤ R) (hRT : R ≤ T) :
    (∫ t : ℝ, weight b c t*‖DirichletPolynomialMeanValue.value S a t‖^2) ≤
      2*(b+c)^2*R^5+
      (∫ t in UniformRealOffCentralEnergy.region T R, ‖DirichletPolynomialMeanValue.value S a t‖^2)+
      Real.exp (-b*T^2)*budget N b := by
  let F := DirichletPolynomialMeanValue.value S a
  let G : ℝ → ℝ := fun t ↦ weight b c t*‖F t‖^2
  let C := Set.Ioc (-R) R
  let B := Set.Ioc (-T) T
  let M := B \ C
  have hC : MeasurableSet C := measurableSet_Ioc
  have hB : MeasurableSet B := measurableSet_Ioc
  have hM : MeasurableSet M := hB.diff hC
  have hT : 0 ≤ T := hR.trans hRT
  have hCS : C ⊆ B := by
    intro t ht
    exact ⟨lt_of_le_of_lt (by linarith only [hRT]) ht.1,ht.2.trans hRT⟩
  have hMS : M ⊆ UniformRealOffCentralEnergy.region T R := by
    intro t ht
    refine ⟨ht.1,?_⟩
    change R ≤ |t|
    by_cases hLeft : t ≤ -R
    · have hh := neg_le_abs t
      linarith only [hh,hLeft]
    · have hRight : R < t := by
        exact lt_of_not_ge (fun htR ↦ ht.2 ⟨lt_of_not_ge hLeft,htR⟩)
      exact hRight.le.trans (le_abs_self t)
  have hFI : IntegrableOn (fun t ↦ ‖F t‖^2) (Set.Icc (-T) T) volume :=
    ((GaussianExponentialSums.polynomial_continuous _ _ _).norm.pow 2).integrableOn_Icc
  have hFE : IntegrableOn (fun t ↦ ‖F t‖^2) (UniformRealOffCentralEnergy.region T R) volume :=
    hFI.mono_set (fun t ht ↦ Set.Ioc_subset_Icc_self ht.1)
  have hFM : IntegrableOn (fun t ↦ ‖F t‖^2) M volume := hFE.mono_set hMS
  have hGI : Integrable G := weighted_integrable S a b c hb hbc
  have hCentral : (∫ t in C, G t) ≤ 2*(b+c)^2*R^5 :=
    central_integral N hN S hS a ha b c R hb.le (hb.le.trans hbc) hR
  have hMiddle : (∫ t in M, G t) ≤
      ∫ t in UniformRealOffCentralEnergy.region T R, ‖F t‖^2 := by
    calc
      _ ≤ ∫ t in M, ‖F t‖^2 := by
        apply integral_mono_ae hGI.integrableOn hFM
        apply Filter.Eventually.of_forall
        intro t
        exact (mul_le_mul_of_nonneg_right (weight_le_one b c t hb.le (hb.le.trans hbc))
          (sq_nonneg _)).trans_eq (one_mul _)
      _ ≤ _ := setIntegral_mono_set (μ := volume) hFE
        (Filter.Eventually.of_forall (fun t ↦ sq_nonneg _)) (Filter.Eventually.of_forall hMS)
  have hTail : (∫ t in Bᶜ, G t) ≤ Real.exp (-b*T^2)*budget N b := by
    have hGaussI := GaussianExponentialSums.gaussian_integrable S (fun n ↦ a n/(n : ℂ))
      (fun n ↦ -Real.log (n : ℝ)) (2*b) (by positivity)
    calc
      _ ≤ ∫ t in Bᶜ, Real.exp (-(2*b)*t^2)*‖F t‖^2 := by
        apply integral_mono_ae hGI.integrableOn hGaussI.integrableOn
        apply Filter.Eventually.of_forall
        intro t
        exact mul_le_mul_of_nonneg_right (weight_gaussian b c t hbc) (sq_nonneg _)
      _ ≤ _ := tail_bound N hN S hS a ha b T hb hT Bᶜ hB.compl (by
        intro t ht
        change ¬(-T<t ∧ t≤T) at ht
        by_cases hLeft : t ≤ -T
        · have hh := neg_le_abs t
          linarith only [hh,hLeft]
        · have hRight : T < t := by
            exact lt_of_not_ge (fun htT ↦ ht ⟨lt_of_not_ge hLeft,htT⟩)
          exact hRight.le.trans (le_abs_self t))
  have hUnion : C ∪ M = B := by
    ext t
    change (t∈C ∨ t∈B ∧ t∉C) ↔ t∈B
    constructor
    · rintro (htC | htM)
      · exact hCS htC
      · exact htM.1
    · intro htB
      by_cases htC : t∈C
      · exact Or.inl htC
      · exact Or.inr ⟨htB,htC⟩
  have hDisjoint : Disjoint C M := Set.disjoint_left.mpr (fun t htC htM ↦ htM.2 htC)
  have hSplit := setIntegral_union hDisjoint hM hGI.integrableOn hGI.integrableOn
  rw [hUnion] at hSplit
  have hAll := integral_add_compl hB hGI
  linarith only [hCentral,hMiddle,hTail,hSplit,hAll]

end PaperP1.GaussianEnergyReduction
