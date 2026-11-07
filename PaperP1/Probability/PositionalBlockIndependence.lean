module

public import PaperP1.Probability.PositionalArrivalIndependence

/-! # Exact independence of finite blocks of Poisson reference coordinates

Two complete finite blocks are independent exactly when all their cross
covariances vanish. This is proved by removing shared zero-rate arrivals and
composing genuinely independent finite arrival tuples. For disjoint blocks
in a pair family, the criterion is exactly the absence of a crossing
positive-rate retained edge, giving the full dependency-graph property.
All statements concern the reference construction and include zero rates.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.PositionalBlockIndependence

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

local instance blockDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def zeroFill {α : Type*} (S T : Finset α) (v : ↥(S\T) → ℕ) : S → ℕ :=
  fun a ↦ if h : a.val∈S\T then v ⟨a.val,h⟩ else 0

theorem measurable_zeroFill {α : Type*} (S T : Finset α) :
    Measurable (zeroFill S T) := by
  classical
  apply Measurable.of_eval
  intro a
  by_cases h : a.val∈S\T
  · simpa only [zeroFill,h,dite_true] using
      (measurable_pi_apply (⟨a.val,h⟩ : ↥(S\T)) :
        Measurable (fun v : ↥(S\T) → ℕ ↦ v ⟨a.val,h⟩))
  · simpa only [zeroFill,h,dite_false] using
      (measurable_const : Measurable (fun _ : ↥(S\T) → ℕ ↦ (0 : ℕ)))

theorem tuple_eq_zeroFill {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a) (poissonMeasure (μ a)) P) (S T : Finset α)
    (hzero : (∑ a∈S∩T,(μ a : ℝ))=0) :
    (fun ω (a : S) ↦ X a.val ω)=ᵐ[P]
      fun ω ↦ zeroFill S T (fun a : ↥(S\T) ↦ X a.val ω) := by
  classical
  have hμ : ∀ a∈S∩T,μ a=0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ ↦ (μ a).property)).mp hzero
    intro a ha
    exact NNReal.coe_injective (h a ha)
  have ha : ∀ a : ↥(S∩T),(X a.val)=ᵐ[P] fun _ ↦ 0 := by
    intro a
    have h := hX a.val
    rw [hμ a.val a.property] at h
    exact PositionalArrivalIndependence.poisson_zero_ae P _ h
  have hall : ∀ᵐ ω ∂P,∀ a : ↥(S∩T),X a.val ω=0 := ae_all_iff.2 ha
  filter_upwards [hall] with ω hω
  funext a
  by_cases h : a.val∈S\T
  · simp only [zeroFill,h,dite_true]
  · have haT : a.val∈T := by
      by_contra hn
      exact h (Finset.mem_sdiff.mpr ⟨a.property,hn⟩)
    simpa only [zeroFill,h,dite_false] using
      hω ⟨a.val,Finset.mem_inter.mpr ⟨a.property,haT⟩⟩

theorem independent_tuples_of_shared_zero {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a) (poissonMeasure (μ a)) P) (hInd : iIndepFun X P)
    (S T : Finset α) (hzero : (∑ a∈S∩T,(μ a : ℝ))=0) :
    IndepFun (fun ω (a : S) ↦ X a.val ω) (fun ω (a : T) ↦ X a.val ω) P := by
  classical
  have h := hInd.indepFun_finset₀ (S\T) T Finset.sdiff_disjoint
    (fun a ↦ (hX a).aemeasurable)
  have hh := h.comp (measurable_zeroFill S T) measurable_id
  change IndepFun (fun ω ↦ zeroFill S T (fun a : ↥(S\T) ↦ X a.val ω))
    (fun ω (a : T) ↦ X a.val ω) P at hh
  exact hh.congr (tuple_eq_zeroFill P μ X hX S T hzero).symm Filter.EventuallyEq.rfl

theorem independent_tuples_iff {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a) (poissonMeasure (μ a)) P) (hInd : iIndepFun X P)
    (S T : Finset α) :
    IndepFun (fun ω (a : S) ↦ X a.val ω) (fun ω (a : T) ↦ X a.val ω) P ↔
      (∑ a∈S∩T,(μ a : ℝ))=0 := by
  constructor
  · intro h
    apply Finset.sum_eq_zero
    intro a ha
    obtain ⟨haS,haT⟩ := Finset.mem_inter.mp ha
    have hc := h.comp (measurable_pi_apply ⟨a,haS⟩) (measurable_pi_apply ⟨a,haT⟩)
    change IndepFun (X a) (X a) P at hc
    have hr := hc.comp (show Measurable (fun n : ℕ ↦ (n : ℝ)) from Measurable.of_discrete)
      (show Measurable (fun n : ℕ ↦ (n : ℝ)) from Measurable.of_discrete)
    change IndepFun (fun ω ↦ (X a ω : ℝ)) (fun ω ↦ (X a ω : ℝ)) P at hr
    have hm := PositionalArrivalCovariance.memLp_two_of_hasLaw P (X a) (μ a) (hX a)
    have hz := hr.covariance_eq_zero hm hm
    rw [covariance_self hm.aemeasurable,
      PositionalArrivalCovariance.variance_of_hasLaw P (X a) (μ a) (hX a)] at hz
    exact hz
  · exact independent_tuples_of_shared_zero P μ X hX hInd S T

def collect {α β : Type*} (F : Finset β) (S : β → Finset α)
    (v : ↥(F.biUnion S) → ℕ) : F → ℕ :=
  fun i ↦ ∑ a : ↥(S i.val),
    v ⟨a.val,Finset.mem_biUnion.mpr ⟨i.val,i.property,a.property⟩⟩

theorem measurable_collect {α β : Type*} (F : Finset β) (S : β → Finset α) :
    Measurable (collect F S) := by
  unfold collect
  fun_prop

theorem collect_tuple {α β Ω : Type*} (F : Finset β) (S : β → Finset α)
    (X : α → Ω → ℕ) :
    (fun ω ↦ collect F S (fun a : ↥(F.biUnion S) ↦ X a.val ω))=
      (fun ω (i : F) ↦ ∑ a∈S i.val,X a ω) := by
  funext ω i
  unfold collect
  exact Finset.sum_coe_sort (S i.val) (fun a ↦ X a ω)

theorem shared_union_zero_iff {α β γ : Type*}
    (μ : α → ℝ≥0) (F : Finset β) (H : Finset γ)
    (S : β → Finset α) (T : γ → Finset α) :
    (∑ a∈(F.biUnion S)∩(H.biUnion T),(μ a : ℝ))=0 ↔
      ∀ i∈F,∀ j∈H,(∑ a∈(S i)∩(T j),(μ a : ℝ))=0 := by
  classical
  constructor
  · intro hz i hi j hj
    have hμ := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ ↦ (μ a).property)).mp hz
    apply Finset.sum_eq_zero
    intro a ha
    obtain ⟨haS,haT⟩ := Finset.mem_inter.mp ha
    exact hμ a (Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨i,hi,haS⟩,
      Finset.mem_biUnion.mpr ⟨j,hj,haT⟩⟩)
  · intro hz
    apply Finset.sum_eq_zero
    intro a ha
    obtain ⟨haF,haH⟩ := Finset.mem_inter.mp ha
    obtain ⟨i,hi,haS⟩ := Finset.mem_biUnion.mp haF
    obtain ⟨j,hj,haT⟩ := Finset.mem_biUnion.mp haH
    have hμ := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ ↦ (μ a).property)).mp (hz i hi j hj)
    exact hμ a (Finset.mem_inter.mpr ⟨haS,haT⟩)

theorem independent_sum_blocks_iff {α β γ Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a) (poissonMeasure (μ a)) P) (hInd : iIndepFun X P)
    (F : Finset β) (H : Finset γ) (S : β → Finset α) (T : γ → Finset α) :
    IndepFun (fun ω (i : F) ↦ ∑ a∈S i.val,X a ω)
      (fun ω (j : H) ↦ ∑ a∈T j.val,X a ω) P ↔
      ∀ i∈F,∀ j∈H,(∑ a∈(S i)∩(T j),(μ a : ℝ))=0 := by
  constructor
  · intro h i hi j hj
    have hc := h.comp (measurable_pi_apply ⟨i,hi⟩) (measurable_pi_apply ⟨j,hj⟩)
    change IndepFun (fun ω ↦ ∑ a∈S i,X a ω) (fun ω ↦ ∑ a∈T j,X a ω) P at hc
    exact (PositionalArrivalIndependence.independent_nat_sums_iff P μ X hX hInd (S i) (T j)).mp hc
  · intro h
    have hz := (shared_union_zero_iff μ F H S T).mpr h
    have ht := independent_tuples_of_shared_zero P μ X hX hInd (F.biUnion S) (H.biUnion T) hz
    have hc := ht.comp (measurable_collect F S) (measurable_collect H T)
    change IndepFun
      (fun ω ↦ collect F S (fun a : ↥(F.biUnion S) ↦ X a.val ω))
      (fun ω ↦ collect H T (fun a : ↥(H.biUnion T) ↦ X a.val ω)) P at hc
    rwa [collect_tuple F S X,collect_tuple H T X] at hc

theorem independent_sum_blocks_iff_pairwise {α β γ Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a) (poissonMeasure (μ a)) P) (hInd : iIndepFun X P)
    (F : Finset β) (H : Finset γ) (S : β → Finset α) (T : γ → Finset α) :
    IndepFun (fun ω (i : F) ↦ ∑ a∈S i.val,X a ω)
      (fun ω (j : H) ↦ ∑ a∈T j.val,X a ω) P ↔
      ∀ i∈F,∀ j∈H,IndepFun (fun ω ↦ ∑ a∈S i,X a ω) (fun ω ↦ ∑ a∈T j,X a ω) P := by
  rw [independent_sum_blocks_iff P μ X hX hInd F H S T]
  simp only [PositionalArrivalIndependence.independent_nat_sums_iff P μ X hX hInd]

def block {ι Ω : Type*} (G : Finset ι) (E : Finset (Finset ι))
    (X : (↥G ⊕ ↥E) → Ω → ℕ) (A : Finset G) : Ω → (A → ℕ) :=
  fun ω x ↦ (∑ a : ↥G ⊕ ↥E,
    X a ω • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val.val

theorem block_eq_sums {ι Ω : Type*} (G : Finset ι) (E : Finset (Finset ι))
    (X : (↥G ⊕ ↥E) → Ω → ℕ) (A : Finset G) :
    block G E X A =
      fun ω (x : A) ↦ ∑ a∈PositionalArrivalMarginals.observedCells G E x.val.val,X a ω := by
  funext ω x
  exact PositionalArrivalMarginals.coordinate_sum G E (fun a ↦ X a ω) x.val

theorem independent_blocks_iff_cross_covariance_zero {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (A B : Finset G) :
    IndepFun (block G E X A) (block G E X B) P ↔
      ∀ x∈A,∀ y∈B,cov[PositionalArrivalCovariance.coordinate G E X x,
        PositionalArrivalCovariance.coordinate G E X y;P]=0 := by
  rw [block_eq_sums G E X A,block_eq_sums G E X B]
  simpa only [PositionalArrivalCovariance.coordinate_eq_sum,
    PositionalArrivalCovariance.covariance_selected_sums P _ X hX hInd] using
    independent_sum_blocks_iff P
      (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq) X hX hInd A B
      (fun x ↦ PositionalArrivalMarginals.observedCells G E x.val)
      (fun x ↦ PositionalArrivalMarginals.observedCells G E x.val)

theorem independent_blocks_iff_pairwise {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (A B : Finset G) :
    IndepFun (block G E X A) (block G E X B) P ↔
      ∀ x∈A,∀ y∈B,IndepFun (PositionalArrivalCovariance.coordinate G E X x)
        (PositionalArrivalCovariance.coordinate G E X y) P := by
  rw [independent_blocks_iff_cross_covariance_zero G E p q hp hq P X hX hInd]
  simp only [PositionalArrivalIndependence.independent_coordinates_iff_covariance_zero
    G E p q hp hq P X hX hInd]

theorem independent_pair_blocks_iff {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (A B : Finset G) (hAB : Disjoint A B) :
    IndepFun (block G E X A) (block G E X B) P ↔
      ∀ x∈A,∀ y∈B,{x.val,y.val}∉E ∨ q {x.val,y.val}=0 := by
  have hxy : ∀ x∈A,∀ y∈B,x≠y := by
    intro x hx y hy h
    subst y
    exact Finset.disjoint_left.mp hAB hx hy
  rw [independent_blocks_iff_pairwise G E p q hp hq P X hX hInd]
  constructor
  · intro h x hx y hy
    exact (PositionalArrivalIndependence.independent_pair_coordinates_iff
      G E p q hp hq hE P X hX hInd x y (hxy x hx y hy)).mp (h x hx y hy)
  · intro h x hx y hy
    exact (PositionalArrivalIndependence.independent_pair_coordinates_iff
      G E p q hp hq hE P X hX hInd x y (hxy x hx y hy)).mpr (h x hx y hy)

theorem independent_pair_blocks_iff_cross_rates_zero {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (A B : Finset G) (hAB : Disjoint A B) :
    IndepFun (block G E X A) (block G E X B) P ↔
      ∀ x∈A,∀ y∈B,{x.val,y.val}∈E → q {x.val,y.val}=0 := by
  rw [independent_pair_blocks_iff G E p q hp hq hE P X hX hInd A B hAB]
  constructor
  · intro h x hx y hy he
    rcases h x hx y hy with hn|hz
    · exact False.elim (hn he)
    · exact hz
  · intro h x hx y hy
    by_cases he : {x.val,y.val}∈E
    · exact Or.inr (h x hx y hy he)
    · exact Or.inl he

theorem independent_pair_blocks_of_no_edges {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (A B : Finset G) (hAB : Disjoint A B)
    (hnone : ∀ x∈A,∀ y∈B,{x.val,y.val}∉E) :
    IndepFun (block G E X A) (block G E X B) P :=
  (independent_pair_blocks_iff G E p q hp hq hE P X hX hInd A B hAB).mpr
    (fun x hx y hy ↦ Or.inl (hnone x hx y hy))

theorem independent_canonical_pair_blocks_iff {ι : Type*}
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2)
    (A B : Finset G) (hAB : Disjoint A B) :
    IndepFun (block G E (fun a ω ↦ ω a) A) (block G E (fun a ω ↦ ω a) B)
      (PaperP1.PositionalPoissonRealization.poissonProduct
        (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq)).val ↔
      ∀ x∈A,∀ y∈B,{x.val,y.val}∈E → q {x.val,y.val}=0 :=
  independent_pair_blocks_iff_cross_rates_zero G E p q hp hq hE _ _
    (PaperP1.PositionalPoissonRealization.poissonProduct_hasLaw_eval _)
    (PaperP1.PositionalPoissonRealization.poissonProduct_independent _) A B hAB

theorem independent_pair_block_events {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (A B : Finset G) (hAB : Disjoint A B)
    (hcross : ∀ x∈A,∀ y∈B,{x.val,y.val}∈E → q {x.val,y.val}=0)
    (C : Set (A → ℕ)) (D : Set (B → ℕ)) (hC : MeasurableSet C) (hD : MeasurableSet D) :
    P ((block G E X A) ⁻¹' C ∩ (block G E X B) ⁻¹' D) =
      P ((block G E X A) ⁻¹' C)*P ((block G E X B) ⁻¹' D) :=
  ((independent_pair_blocks_iff_cross_rates_zero G E p q hp hq hE P X hX hInd A B hAB).mpr
    hcross).measure_inter_preimage_eq_mul C D hC hD

theorem independent_pair_blocks_iff_no_positive_crossing {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (A B : Finset G) (hAB : Disjoint A B) :
    IndepFun (block G E X A) (block G E X B) P ↔
      ∀ x∈A,∀ y∈B,¬({x.val,y.val}∈E ∧ 0<q {x.val,y.val}) := by
  rw [independent_pair_blocks_iff_cross_rates_zero G E p q hp hq hE P X hX hInd A B hAB]
  constructor
  · intro h x hx y hy he
    exact (ne_of_gt he.2) (h x hx y hy he.1)
  · intro h x hx y hy he
    have hn : ¬0<q {x.val,y.val} := fun hpq ↦ h x hx y hy ⟨he,hpq⟩
    exact le_antisymm (le_of_not_gt hn) (hq _ he)

end PaperP1.PositionalBlockIndependence
