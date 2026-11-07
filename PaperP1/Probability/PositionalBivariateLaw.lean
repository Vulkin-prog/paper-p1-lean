module

public import PaperP1.Probability.PositionalArrivalIndependence

/-! # Exact bivariate laws of independent Poisson arrival sums

This development concerns the reference arrival field. It makes no assertion
that the arithmetic indicators themselves have Poisson joint laws.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.PositionalBivariateLaw

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

local instance bivariateDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def addCommon (z : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  (z.1 + z.2.2, z.2.1 + z.2.2)

theorem measurable_addCommon : Measurable addCommon := by
  unfold addCommon
  fun_prop

def law (a b c : ℝ≥0) : Measure (ℕ × ℕ) :=
  Measure.map addCommon ((poissonMeasure a).prod ((poissonMeasure b).prod (poissonMeasure c)))

theorem hasLaw_addCommon (a b c : ℝ≥0) :
    HasLaw addCommon (law a b c)
      ((poissonMeasure a).prod ((poissonMeasure b).prod (poissonMeasure c))) :=
  hasLaw_map measurable_addCommon.aemeasurable

theorem law_isProbability (a b c : ℝ≥0) : IsProbabilityMeasure (law a b c) :=
  (hasLaw_addCommon a b c).isProbabilityMeasure_iff.mp inferInstance

theorem sum_partition {α M : Type*} [DecidableEq α] [AddCommMonoid M] (S T : Finset α) (f : α → M) :
    (∑ i∈S\T,f i)+(∑ i∈S∩T,f i)=∑ i∈S,f i := by
  classical
  have hdis : Disjoint (S\T) (S∩T) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hj).2
  rw [← Finset.sum_union hdis]
  congr 1
  ext i
  simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
  tauto

theorem sum_union_filter_left {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (S T : Finset α) (f : α → M) :
    (∑ i∈S∪T,if i∈S then f i else 0)=∑ i∈S,f i := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

theorem independent_sum_pair {α Ω : Type*} [DecidableEq α] [MeasurableSpace Ω]
    (P : Measure Ω) (X : α → Ω → ℕ) (hX : ∀ a,AEMeasurable (X a) P)
    (hInd : iIndepFun X P) (S T U : Finset α)
    (hST : Disjoint S T) (hSU : Disjoint S U) :
    IndepFun (fun ω ↦ ∑ i∈S,X i ω)
      (fun ω ↦ (∑ i∈T,X i ω,∑ i∈U,X i ω)) P := by
  classical
  have hdis : Disjoint S (T∪U) := Finset.disjoint_union_right.mpr ⟨hST,hSU⟩
  have h := hInd.indepFun_finset₀ S (T∪U) hdis hX
  have hl : Measurable (fun v : S → ℕ ↦ ∑ i : S,v i) := by fun_prop
  have hr : Measurable (fun v : ↥(T∪U) → ℕ ↦
      (∑ i : ↥(T∪U),if i.val∈T then v i else 0,
       ∑ i : ↥(T∪U),if i.val∈U then v i else 0)) := by fun_prop
  have hh := h.comp hl hr
  have hleft (ω : Ω) : (∑ i : S,X i.val ω)=∑ i∈S,X i ω :=
    Finset.sum_coe_sort S (fun i ↦ X i ω)
  have hright (ω : Ω) :
      (∑ i : ↥(T∪U),if i.val∈T then X i.val ω else 0)=∑ i∈T,X i ω := by
    calc
      _ = ∑ i∈T∪U,if i∈T then X i ω else 0 :=
        Finset.sum_coe_sort (T∪U) (fun i ↦ if i∈T then X i ω else 0)
      _ = _ := sum_union_filter_left T U (fun i ↦ X i ω)
  have hthird (ω : Ω) :
      (∑ i : ↥(T∪U),if i.val∈U then X i.val ω else 0)=∑ i∈U,X i ω := by
    calc
      _ = ∑ i∈T∪U,if i∈U then X i ω else 0 :=
        Finset.sum_coe_sort (T∪U) (fun i ↦ if i∈U then X i ω else 0)
      _ = _ := by
        rw [Finset.union_comm T U]
        exact sum_union_filter_left U T (fun i ↦ X i ω)
  change IndepFun (fun ω ↦ ∑ i : S,X i.val ω)
    (fun ω ↦ (∑ i : ↥(T∪U),if i.val∈T then X i.val ω else 0,
      ∑ i : ↥(T∪U),if i.val∈U then X i.val ω else 0)) P at hh
  simpa only [hleft,hright,hthird] using hh

theorem hasLaw_pair_sums {α Ω : Type*} [DecidableEq α] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ i,HasLaw (X i) (poissonMeasure (μ i)) P) (hInd : iIndepFun X P)
    (S T : Finset α) :
    HasLaw (fun ω ↦ (∑ i∈S,X i ω,∑ i∈T,X i ω))
      (law (∑ i∈S\T,μ i) (∑ i∈T\S,μ i) (∑ i∈S∩T,μ i)) P := by
  classical
  have hLR : Disjoint (S\T) (T\S) :=
    Finset.disjoint_of_subset_right Finset.sdiff_subset Finset.sdiff_disjoint
  have hLC : Disjoint (S\T) (S∩T) :=
    Finset.disjoint_of_subset_right Finset.inter_subset_right Finset.sdiff_disjoint
  have hRC : Disjoint (T\S) (S∩T) :=
    Finset.disjoint_of_subset_right Finset.inter_subset_left Finset.sdiff_disjoint
  have hA := PositionalArrivalMarginals.hasLaw_sum P (S\T) μ X hX hInd
  have hB := PositionalArrivalMarginals.hasLaw_sum P (T\S) μ X hX hInd
  have hC := PositionalArrivalMarginals.hasLaw_sum P (S∩T) μ X hX hInd
  have hBCind := PositionalArrivalIndependence.independent_disjoint_sums P X
    (fun i ↦ (hX i).aemeasurable) hInd (T\S) (S∩T) hRC
  have hBC := hBCind.hasLaw_prod hB hC
  have hABCind := independent_sum_pair P X (fun i ↦ (hX i).aemeasurable) hInd
    (S\T) (T\S) (S∩T) hLR hLC
  have hABC := hABCind.hasLaw_prod hA hBC
  have hh := (hasLaw_addCommon (∑ i∈S\T,μ i) (∑ i∈T\S,μ i) (∑ i∈S∩T,μ i)).fun_comp hABC
  change HasLaw (fun ω ↦ ((∑ i∈S\T,X i ω)+(∑ i∈S∩T,X i ω),
    (∑ i∈T\S,X i ω)+(∑ i∈S∩T,X i ω))) _ P at hh
  have hfirst (ω : Ω) := sum_partition S T (fun i ↦ X i ω)
  have hsecond (ω : Ω) :
      (∑ i∈T\S,X i ω)+(∑ i∈S∩T,X i ω)=∑ i∈T,X i ω := by
    simpa only [Finset.inter_comm T S] using sum_partition T S (fun i ↦ X i ω)
  simpa only [hfirst,hsecond] using hh

def count {ι Ω : Type*} (G : Finset ι) (E : Finset (Finset ι))
    (X : (↥G ⊕ ↥E) → Ω → ℕ) (x : G) : Ω → ℕ :=
  fun ω ↦ (∑ a : ↥G ⊕ ↥E,
    X a ω • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val

theorem count_eq_sum {ι Ω : Type*} (G : Finset ι) (E : Finset (Finset ι))
    (X : (↥G ⊕ ↥E) → Ω → ℕ) (x : G) :
    count G E X x = fun ω ↦ ∑ a∈PositionalArrivalMarginals.observedCells G E x.val,X a ω := by
  funext ω
  exact PositionalArrivalMarginals.coordinate_sum G E (fun a ↦ X a ω) x

theorem field_bivariate_parameters {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x y : G) :
    ∃ a b c : ℝ≥0,(a : ℝ)+(c : ℝ)=p x.val ∧ (b : ℝ)+(c : ℝ)=p y.val ∧
      (c : ℝ)=cov[PositionalArrivalCovariance.coordinate G E X x,
        PositionalArrivalCovariance.coordinate G E X y;P] ∧
      HasLaw (fun ω ↦ (count G E X x ω,count G E X y ω)) (law a b c) P := by
  classical
  let μ := PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq
  let S := PositionalArrivalMarginals.observedCells G E x.val
  let T := PositionalArrivalMarginals.observedCells G E y.val
  let a : ℝ≥0 := ∑ i∈S\T,μ i
  let b : ℝ≥0 := ∑ i∈T\S,μ i
  let c : ℝ≥0 := ∑ i∈S∩T,μ i
  refine ⟨a,b,c,?_,?_,?_,?_⟩
  · have hac : a+c=∑ i∈S,μ i := sum_partition S T μ
    calc
      (a : ℝ)+(c : ℝ)=((a+c : ℝ≥0) : ℝ) := rfl
      _ = ((∑ i∈S,μ i : ℝ≥0) : ℝ) := congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) hac
      _ = p x.val := PositionalArrivalMarginals.rate_sum_observed G E p q hp hq x
  · have hbc : b+c=∑ i∈T,μ i := by
      dsimp only [b,c]
      simpa only [Finset.inter_comm T S] using sum_partition T S μ
    calc
      (b : ℝ)+(c : ℝ)=((b+c : ℝ≥0) : ℝ) := rfl
      _ = ((∑ i∈T,μ i : ℝ≥0) : ℝ) := congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) hbc
      _ = p y.val := PositionalArrivalMarginals.rate_sum_observed G E p q hp hq y
  · change ((∑ i∈S∩T,μ i : ℝ≥0) : ℝ)=_
    rw [NNReal.coe_sum,PositionalArrivalCovariance.coordinate_eq_sum,
      PositionalArrivalCovariance.coordinate_eq_sum,
      PositionalArrivalCovariance.covariance_selected_sums P μ X hX hInd]
    have hd : (fun a b : ↥G ⊕ ↥E ↦ PositionalArrivalCovariance.covarianceDecidable (a=b)) =
        (inferInstance : DecidableEq (↥G ⊕ ↥E)) := Subsingleton.elim _ _
    rw [hd]
  · simpa only [count_eq_sum,S,T,a,b,c] using hasLaw_pair_sums P μ X hX hInd S T

theorem field_covariance_bounds {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x y : G) :
    let r := cov[PositionalArrivalCovariance.coordinate G E X x,
      PositionalArrivalCovariance.coordinate G E X y;P]
    0≤r ∧ r≤p x.val ∧ r≤p y.val := by
  obtain ⟨a,b,c,hx,hy,hc,_hlaw⟩ := field_bivariate_parameters G E p q hp hq P X hX hInd x y
  dsimp only
  rw [← hc]
  refine ⟨c.property,?_,?_⟩
  · calc
      (c : ℝ)≤(a : ℝ)+(c : ℝ) := le_add_of_nonneg_left a.property
      _ = p x.val := hx
  · calc
      (c : ℝ)≤(b : ℝ)+(c : ℝ) := le_add_of_nonneg_left b.property
      _ = p y.val := hy

theorem field_joint_law {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x y : G) :
    let r := (cov[PositionalArrivalCovariance.coordinate G E X x,
      PositionalArrivalCovariance.coordinate G E X y;P]).toNNReal
    HasLaw (fun ω ↦ (count G E X x ω,count G E X y ω))
      (law ((p x.val).toNNReal-r) ((p y.val).toNNReal-r) r) P := by
  obtain ⟨a,b,c,hx,hy,hc,hlaw⟩ := field_bivariate_parameters G E p q hp hq P X hX hInd x y
  have ha : a=(p x.val).toNNReal-c := by
    rw [← hx,← NNReal.coe_add,Real.toNNReal_coe]
    simp
  have hb : b=(p y.val).toNNReal-c := by
    rw [← hy,← NNReal.coe_add,Real.toNNReal_coe]
    simp
  have hc' : c=(cov[PositionalArrivalCovariance.coordinate G E X x,
      PositionalArrivalCovariance.coordinate G E X y;P]).toNNReal := by
    rw [← hc,Real.toNNReal_coe]
  simpa only [ha,hb,hc'] using hlaw

theorem pair_matrix_joint_law {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x y : G) :
    let r : ℝ := if x=y then p x.val else if {x.val,y.val}∈E then q {x.val,y.val} else 0
    HasLaw (fun ω ↦ (count G E X x ω,count G E X y ω))
      (law ((p x.val).toNNReal-r.toNNReal) ((p y.val).toNNReal-r.toNNReal) r.toNNReal) P := by
  have hr := PositionalArrivalCovariance.covariance_pair_matrix G E p q hp hq hE P X hX hInd x y
  have hd : PositionalArrivalCovariance.covarianceDecidable=bivariateDecidable := Subsingleton.elim _ _
  rw [hd] at hr
  simpa only [hr] using field_joint_law G E p q hp hq P X hX hInd x y

theorem canonical_pair_joint_law {ι : Type*}
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2) (x y : G) :
    let r : ℝ := if x=y then p x.val else if {x.val,y.val}∈E then q {x.val,y.val} else 0
    HasLaw (fun ω : (↥G ⊕ ↥E) → ℕ ↦
      (count G E (fun a (v : (↥G ⊕ ↥E) → ℕ) ↦ v a) x ω,
       count G E (fun a (v : (↥G ⊕ ↥E) → ℕ) ↦ v a) y ω))
      (law ((p x.val).toNNReal-r.toNNReal) ((p y.val).toNNReal-r.toNNReal) r.toNNReal)
      (PaperP1.PositionalPoissonRealization.poissonProduct
        (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq)) := by
  let μ := PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq
  let P : Measure ((↥G ⊕ ↥E) → ℕ) := PaperP1.PositionalPoissonRealization.poissonProduct μ
  have hX : ∀ a,HasLaw (fun ω : (↥G ⊕ ↥E) → ℕ ↦ ω a) (poissonMeasure (μ a)) P :=
    PaperP1.PositionalPoissonRealization.poissonProduct_hasLaw_eval μ
  have hInd : iIndepFun (fun a (ω : (↥G ⊕ ↥E) → ℕ) ↦ ω a) P :=
    PaperP1.PositionalPoissonRealization.poissonProduct_independent μ
  exact pair_matrix_joint_law G E p q hp hq hE P
    (fun a (ω : (↥G ⊕ ↥E) → ℕ) ↦ ω a) hX hInd x y

end PaperP1.PositionalBivariateLaw
