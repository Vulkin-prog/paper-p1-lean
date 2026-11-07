module

public import PaperP1.Probability.PositionalArrivalCovariance

/-! # Exact independence criterion for Poisson reference arrivals

For these reference fields, two coordinates are independent exactly when their
shared Poisson intensity is zero. In the pair case this identifies precisely
the positive-rate retained edges as the dependence graph, including degenerate
zero rates. Both natural-valued counts and real-valued coordinates are covered.
The criterion is proved for the actual independent arrivals and is not a
general assertion that zero covariance implies independence.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.PositionalArrivalIndependence

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

local instance independenceDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem independent_disjoint_sums {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : α → Ω → ℕ) (hX : ∀ a,AEMeasurable (X a) P)
    (hInd : iIndepFun X P) (S T : Finset α) (hST : Disjoint S T) :
    IndepFun (fun ω ↦ ∑ a∈S,X a ω) (fun ω ↦ ∑ a∈T,X a ω) P := by
  classical
  have h := hInd.indepFun_finset₀ S T hST hX
  have hS : Measurable (fun v : S → ℕ ↦ ∑ a : S,v a) := by fun_prop
  have hT : Measurable (fun v : T → ℕ ↦ ∑ a : T,v a) := by fun_prop
  have hh := h.comp hS hT
  have hs : (fun ω ↦ ∑ a : S,X a ω)=(fun ω ↦ ∑ a∈S,X a ω) := by
    funext ω
    exact Finset.sum_coe_sort S (fun a ↦ X a ω)
  have ht : (fun ω ↦ ∑ a : T,X a ω)=(fun ω ↦ ∑ a∈T,X a ω) := by
    funext ω
    exact Finset.sum_coe_sort T (fun a ↦ X a ω)
  change IndepFun (fun ω ↦ ∑ a : S,X a ω) (fun ω ↦ ∑ a : T,X a ω) P at hh
  rwa [hs,ht] at hh

theorem poisson_zero_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℕ) (hY : HasLaw Y (poissonMeasure 0) P) :
    Y =ᵐ[P] fun _ ↦ 0 := by
  rw [PositionalArrivalMarginals.poisson_zero] at hY
  exact hY.ae_eq_of_dirac

theorem sum_eq_sdiff_of_shared_zero {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a) (poissonMeasure (μ a)) P) (S T : Finset α)
    (hzero : (∑ a∈S∩T,(μ a : ℝ))=0) :
    (fun ω ↦ ∑ a∈S,X a ω)=ᵐ[P] (fun ω ↦ ∑ a∈S\T,X a ω) := by
  classical
  have hμ : ∀ a∈S∩T,μ a=0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ ↦ (μ a).property)).mp hzero
    intro a ha
    exact NNReal.coe_injective (h a ha)
  have ha : ∀ a : ↥(S∩T),(X a.val)=ᵐ[P] fun _ ↦ 0 := by
    intro a
    have h := hX a.val
    rw [hμ a.val a.property] at h
    exact poisson_zero_ae P _ h
  have hall : ∀ᵐ ω ∂P,∀ a : ↥(S∩T),X a.val ω=0 := by
    exact ae_all_iff.2 ha
  filter_upwards [hall] with ω hω
  symm
  apply Finset.sum_subset Finset.sdiff_subset
  intro a haS haDiff
  have haT : a∈T := by
    by_contra hn
    exact haDiff (Finset.mem_sdiff.mpr ⟨haS,hn⟩)
  exact hω ⟨a,Finset.mem_inter.mpr ⟨haS,haT⟩⟩

theorem independent_sums_of_shared_zero {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a) (poissonMeasure (μ a)) P) (hInd : iIndepFun X P)
    (S T : Finset α) (hzero : (∑ a∈S∩T,(μ a : ℝ))=0) :
    IndepFun (fun ω ↦ ∑ a∈S,X a ω) (fun ω ↦ ∑ a∈T,X a ω) P := by
  classical
  have hST : Disjoint (S\T) T := Finset.sdiff_disjoint
  have h := independent_disjoint_sums P X (fun a ↦ (hX a).aemeasurable) hInd (S\T) T hST
  exact h.congr (sum_eq_sdiff_of_shared_zero P μ X hX S T hzero).symm Filter.EventuallyEq.rfl

theorem memLp_real_sum {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a) (poissonMeasure (μ a)) P) (S : Finset α) :
    MemLp (fun ω ↦ ∑ a∈S,(X a ω : ℝ)) 2 P := by
  exact memLp_finsetSum S (fun a _ ↦
    PositionalArrivalCovariance.memLp_two_of_hasLaw P (X a) (μ a) (hX a))

theorem cast_sum {α Ω : Type*} (X : α → Ω → ℕ) (S : Finset α) :
    (fun ω ↦ ((∑ a∈S,X a ω : ℕ) : ℝ))=(fun ω ↦ ∑ a∈S,(X a ω : ℝ)) := by
  funext ω
  simp only [Nat.cast_sum]

theorem independent_real_sums_iff {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a) (poissonMeasure (μ a)) P) (hInd : iIndepFun X P)
    (S T : Finset α) :
    IndepFun (fun ω ↦ ∑ a∈S,(X a ω : ℝ)) (fun ω ↦ ∑ a∈T,(X a ω : ℝ)) P ↔
      (∑ a∈S∩T,(μ a : ℝ))=0 := by
  constructor
  · intro h
    have hz := h.covariance_eq_zero (memLp_real_sum P μ X hX S) (memLp_real_sum P μ X hX T)
    rw [PositionalArrivalCovariance.covariance_selected_sums P μ X hX hInd] at hz
    exact hz
  · intro hzero
    have h := independent_sums_of_shared_zero P μ X hX hInd S T hzero
    have hh := h.comp (show Measurable (fun n : ℕ ↦ (n : ℝ)) from Measurable.of_discrete)
      (show Measurable (fun n : ℕ ↦ (n : ℝ)) from Measurable.of_discrete)
    change IndepFun (fun ω ↦ ((∑ a∈S,X a ω : ℕ) : ℝ))
      (fun ω ↦ ((∑ a∈T,X a ω : ℕ) : ℝ)) P at hh
    rwa [cast_sum X S,cast_sum X T] at hh

theorem independent_nat_sums_iff {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a) (poissonMeasure (μ a)) P) (hInd : iIndepFun X P)
    (S T : Finset α) :
    IndepFun (fun ω ↦ ∑ a∈S,X a ω) (fun ω ↦ ∑ a∈T,X a ω) P ↔
      (∑ a∈S∩T,(μ a : ℝ))=0 := by
  constructor
  · intro h
    have hh := h.comp (show Measurable (fun n : ℕ ↦ (n : ℝ)) from Measurable.of_discrete)
      (show Measurable (fun n : ℕ ↦ (n : ℝ)) from Measurable.of_discrete)
    change IndepFun (fun ω ↦ ((∑ a∈S,X a ω : ℕ) : ℝ))
      (fun ω ↦ ((∑ a∈T,X a ω : ℕ) : ℝ)) P at hh
    rw [cast_sum X S,cast_sum X T] at hh
    exact (independent_real_sums_iff P μ X hX hInd S T).mp hh
  · exact independent_sums_of_shared_zero P μ X hX hInd S T

theorem independent_real_sums_iff_covariance_zero {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a) (poissonMeasure (μ a)) P) (hInd : iIndepFun X P)
    (S T : Finset α) :
    IndepFun (fun ω ↦ ∑ a∈S,(X a ω : ℝ)) (fun ω ↦ ∑ a∈T,(X a ω : ℝ)) P ↔
      cov[fun ω ↦ ∑ a∈S,(X a ω : ℝ),fun ω ↦ ∑ a∈T,(X a ω : ℝ);P]=0 := by
  rw [PositionalArrivalCovariance.covariance_selected_sums P μ X hX hInd]
  exact independent_real_sums_iff P μ X hX hInd S T

theorem independent_coordinates_iff_covariance_zero {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x y : G) :
    IndepFun (PositionalArrivalCovariance.coordinate G E X x)
      (PositionalArrivalCovariance.coordinate G E X y) P ↔
      cov[PositionalArrivalCovariance.coordinate G E X x,
        PositionalArrivalCovariance.coordinate G E X y;P]=0 := by
  rw [PositionalArrivalCovariance.coordinate_eq_sum G E X x,
    PositionalArrivalCovariance.coordinate_eq_sum G E X y]
  exact independent_real_sums_iff_covariance_zero P _ X hX hInd _ _

theorem independent_distinct_coordinates_iff {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x y : G) (hxy : x≠y) :
    IndepFun (PositionalArrivalCovariance.coordinate G E X x)
      (PositionalArrivalCovariance.coordinate G E X y) P ↔
      (∑ e∈E,if x.val∈e ∧ y.val∈e then q e else 0)=0 := by
  rw [independent_coordinates_iff_covariance_zero G E p q hp hq P X hX hInd x y,
    PositionalArrivalCovariance.covariance_coordinates G E p q hp hq P X hX hInd,
    ite_eq_right hxy,zero_add]

theorem independent_pair_coordinates_iff {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x y : G) (hxy : x≠y) :
    IndepFun (PositionalArrivalCovariance.coordinate G E X x)
      (PositionalArrivalCovariance.coordinate G E X y) P ↔
      {x.val,y.val}∉E ∨ q {x.val,y.val}=0 := by
  rw [independent_coordinates_iff_covariance_zero G E p q hp hq P X hX hInd x y,
    PositionalArrivalCovariance.covariance_pairs G E p q hp hq hE P X hX hInd x y hxy]
  by_cases he : {x.val,y.val}∈E <;> simp [he]

theorem self_independent_coordinate_iff {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x : G) :
    IndepFun (PositionalArrivalCovariance.coordinate G E X x)
      (PositionalArrivalCovariance.coordinate G E X x) P ↔ p x.val=0 := by
  rw [independent_coordinates_iff_covariance_zero G E p q hp hq P X hX hInd x x,
    covariance_self (PositionalArrivalCovariance.memLp_coordinate G E p q hp hq P X hX hInd x).aemeasurable,
    PositionalArrivalCovariance.variance_coordinate G E p q hp hq P X hX hInd x]

theorem independent_canonical_pairs_iff {ι : Type*}
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2) (x y : G) (hxy : x≠y) :
    IndepFun (PositionalArrivalCovariance.coordinate G E (fun a ω ↦ ω a) x)
      (PositionalArrivalCovariance.coordinate G E (fun a ω ↦ ω a) y)
      (PaperP1.PositionalPoissonRealization.poissonProduct
        (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq)).val ↔
      {x.val,y.val}∉E ∨ q {x.val,y.val}=0 :=
  independent_pair_coordinates_iff G E p q hp hq hE _ _
    (PaperP1.PositionalPoissonRealization.poissonProduct_hasLaw_eval _)
    (PaperP1.PositionalPoissonRealization.poissonProduct_independent _) x y hxy

theorem independent_count_coordinates_iff {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x y : G) :
    IndepFun
      (fun ω ↦ (∑ a : ↥G ⊕ ↥E,
        X a ω • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val)
      (fun ω ↦ (∑ a : ↥G ⊕ ↥E,
        X a ω • PaperP1.PositionalPoissonRealization.channelJump G E a) y.val) P ↔
      IndepFun (PositionalArrivalCovariance.coordinate G E X x)
        (PositionalArrivalCovariance.coordinate G E X y) P := by
  have hx : (fun ω ↦ (∑ a : ↥G ⊕ ↥E,
        X a ω • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val)=
      (fun ω ↦ ∑ a∈PositionalArrivalMarginals.observedCells G E x.val,X a ω) := by
    funext ω
    exact PositionalArrivalMarginals.coordinate_sum G E (fun a ↦ X a ω) x
  have hy : (fun ω ↦ (∑ a : ↥G ⊕ ↥E,
        X a ω • PaperP1.PositionalPoissonRealization.channelJump G E a) y.val)=
      (fun ω ↦ ∑ a∈PositionalArrivalMarginals.observedCells G E y.val,X a ω) := by
    funext ω
    exact PositionalArrivalMarginals.coordinate_sum G E (fun a ↦ X a ω) y
  rw [hx,hy,independent_nat_sums_iff P _ X hX hInd,
    PositionalArrivalCovariance.coordinate_eq_sum G E X x,
    PositionalArrivalCovariance.coordinate_eq_sum G E X y,
    independent_real_sums_iff P _ X hX hInd]

theorem independent_pair_counts_iff {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x y : G) (hxy : x≠y) :
    IndepFun
      (fun ω ↦ (∑ a : ↥G ⊕ ↥E,
        X a ω • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val)
      (fun ω ↦ (∑ a : ↥G ⊕ ↥E,
        X a ω • PaperP1.PositionalPoissonRealization.channelJump G E a) y.val) P ↔
      {x.val,y.val}∉E ∨ q {x.val,y.val}=0 := by
  rw [independent_count_coordinates_iff G E p q hp hq P X hX hInd,
    independent_pair_coordinates_iff G E p q hp hq hE P X hX hInd x y hxy]

theorem independent_canonical_distinct_iff {ι : Type*}
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (x y : G) (hxy : x≠y) :
    IndepFun (PositionalArrivalCovariance.coordinate G E (fun a ω ↦ ω a) x)
      (PositionalArrivalCovariance.coordinate G E (fun a ω ↦ ω a) y)
      (PaperP1.PositionalPoissonRealization.poissonProduct
        (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq)).val ↔
      (∑ e∈E,if x.val∈e ∧ y.val∈e then q e else 0)=0 :=
  independent_distinct_coordinates_iff G E p q hp hq _ _
    (PaperP1.PositionalPoissonRealization.poissonProduct_hasLaw_eval _)
    (PaperP1.PositionalPoissonRealization.poissonProduct_independent _) x y hxy

theorem dependent_pair_coordinates_iff {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x y : G) (hxy : x≠y) :
    ¬IndepFun (PositionalArrivalCovariance.coordinate G E X x)
      (PositionalArrivalCovariance.coordinate G E X y) P ↔
      {x.val,y.val}∈E ∧ 0<q {x.val,y.val} := by
  rw [independent_pair_coordinates_iff G E p q hp hq hE P X hX hInd x y hxy,
    not_or,not_not]
  constructor
  · rintro ⟨he,hne⟩
    exact ⟨he,lt_of_le_of_ne (hq _ he) (Ne.symm hne)⟩
  · rintro ⟨he,hpos⟩
    exact ⟨he,ne_of_gt hpos⟩

end PaperP1.PositionalArrivalIndependence
