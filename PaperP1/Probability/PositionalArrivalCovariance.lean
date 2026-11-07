module

public import PaperP1.Probability.PositionalArrivalMarginals
public import Mathlib.Probability.Moments.Variance

/-! # Exact covariance matrix of compensated reference arrival fields

The coordinates are square integrable in every independent Poisson realization.
For arbitrary finite packets their covariance is the sum of shared arrival
rates, including the compensated single rate on the diagonal. For pairs the
diagonal is the original intensity and each off-diagonal entry is the retained
pair rate. These identities concern the reference field, not the original
arithmetic indicators. No countability of the ambient configuration space is
required.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.PositionalArrivalCovariance

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

local instance covarianceDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem square_eq_factorial_two (n : ℕ) :
    (n : ℝ)^2=(n.descFactorial 2 : ℝ)+(n : ℝ) := by
  cases n with
  | zero => norm_num
  | succ n =>
    simp [Nat.descFactorial_succ]
    ring

theorem mean_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℕ) (r : ℝ≥0) (hY : HasLaw Y (poissonMeasure r) P) :
    Integrable (fun ω ↦ (Y ω : ℝ)) P ∧ (∫ ω,(Y ω : ℝ) ∂P)=(r : ℝ) := by
  simpa only [Nat.descFactorial_one,pow_one] using
    PositionalArrivalMarginals.factorial_moment_of_hasLaw P Y r hY 1

theorem second_moment_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℕ) (r : ℝ≥0) (hY : HasLaw Y (poissonMeasure r) P) :
    Integrable (fun ω ↦ (Y ω : ℝ)^2) P ∧
      (∫ ω,(Y ω : ℝ)^2 ∂P)=(r : ℝ)^2+(r : ℝ) := by
  obtain ⟨h1,e1⟩ := mean_of_hasLaw P Y r hY
  obtain ⟨h2,e2⟩ := PositionalArrivalMarginals.factorial_moment_of_hasLaw P Y r hY 2
  have heq : (fun ω ↦ (Y ω : ℝ)^2)=
      (fun ω ↦ ((Y ω).descFactorial 2 : ℝ)+(Y ω : ℝ)) := by
    funext ω
    exact square_eq_factorial_two (Y ω)
  rw [heq]
  exact ⟨h2.add h1,by rw [integral_add h2 h1,e2,e1]⟩

theorem memLp_two_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℕ) (r : ℝ≥0) (hY : HasLaw Y (poissonMeasure r) P) :
    MemLp (fun ω ↦ (Y ω : ℝ)) 2 P :=
  (memLp_two_iff_integrable_sq (mean_of_hasLaw P Y r hY).1.aestronglyMeasurable).2
    (second_moment_of_hasLaw P Y r hY).1

theorem variance_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℕ) (r : ℝ≥0)
    (hY : HasLaw Y (poissonMeasure r) P) :
    Var[fun ω ↦ (Y ω : ℝ); P]=(r : ℝ) := by
  rw [variance_eq_sub (memLp_two_of_hasLaw P Y r hY)]
  change (∫ ω,(Y ω : ℝ)^2 ∂P)-(∫ ω,(Y ω : ℝ) ∂P)^2=(r : ℝ)
  rw [(second_moment_of_hasLaw P Y r hY).2,(mean_of_hasLaw P Y r hY).2]
  ring

theorem covariance_cells {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a) (poissonMeasure (μ a)) P) (hInd : iIndepFun X P) (a b : α) :
    cov[fun ω ↦ (X a ω : ℝ),fun ω ↦ (X b ω : ℝ);P]=if a=b then (μ a : ℝ) else 0 := by
  by_cases hab : a=b
  · subst b
    rw [covariance_self (memLp_two_of_hasLaw P (X a) (μ a) (hX a)).aemeasurable,
      variance_of_hasLaw P (X a) (μ a) (hX a),ite_eq_left rfl]
  · rw [ite_eq_right hab]
    have hreal := hInd.comp (fun _ (n : ℕ) ↦ (n : ℝ)) (fun _ ↦ Measurable.of_discrete)
    exact (hreal.indepFun hab).covariance_eq_zero
      (memLp_two_of_hasLaw P (X a) (μ a) (hX a))
      (memLp_two_of_hasLaw P (X b) (μ b) (hX b))

theorem covariance_selected_sums {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a) (poissonMeasure (μ a)) P) (hInd : iIndepFun X P)
    (S T : Finset α) :
    cov[fun ω ↦ ∑ a∈S,(X a ω : ℝ),fun ω ↦ ∑ a∈T,(X a ω : ℝ);P]=
      ∑ a∈S∩T,(μ a : ℝ) := by
  classical
  rw [covariance_fun_sum_fun_sum'
    (fun a _ ↦ memLp_two_of_hasLaw P (X a) (μ a) (hX a))
    (fun a _ ↦ memLp_two_of_hasLaw P (X a) (μ a) (hX a))]
  simp_rw [covariance_cells P μ X hX hInd]
  simp only [Finset.sum_ite_eq]
  have hfilter : S.filter (fun a ↦ a∈T)=S∩T := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_inter]
  rw [← Finset.sum_filter,hfilter]

def coordinate {ι Ω : Type*} (G : Finset ι) (E : Finset (Finset ι))
    (X : (↥G ⊕ ↥E) → Ω → ℕ) (x : G) : Ω → ℝ :=
  fun ω ↦ ((∑ a : ↥G ⊕ ↥E,
    X a ω • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val : ℝ)

theorem coordinate_eq_sum {ι Ω : Type*} (G : Finset ι) (E : Finset (Finset ι))
    (X : (↥G ⊕ ↥E) → Ω → ℕ) (x : G) :
    coordinate G E X x =
      fun ω ↦ ∑ a∈PositionalArrivalMarginals.observedCells G E x.val,(X a ω : ℝ) := by
  funext ω
  unfold coordinate
  rw [PositionalArrivalMarginals.coordinate_sum]
  simp only [Nat.cast_sum]

theorem sum_observed_inter {ι : Type*} (G : Finset ι) (E : Finset (Finset ι))
    (w : (↥G ⊕ ↥E) → ℝ) (x y : G) :
    (∑ a∈PositionalArrivalMarginals.observedCells G E x.val ∩
      PositionalArrivalMarginals.observedCells G E y.val,w a) =
      (if x=y then w (Sum.inl x) else 0)+
        ∑ e : E,if x.val∈e.val ∧ y.val∈e.val then w (Sum.inr e) else 0 := by
  classical
  have hs : PositionalArrivalMarginals.observedCells G E x.val ∩
      PositionalArrivalMarginals.observedCells G E y.val =
      (PositionalArrivalMarginals.observedCells G E x.val).filter
        (fun a ↦ a∈PositionalArrivalMarginals.observedCells G E y.val) := by
    ext a
    simp only [Finset.mem_inter,Finset.mem_filter]
  rw [hs,Finset.sum_filter,PositionalArrivalMarginals.sum_observed]
  congr 1
  · by_cases hxy : x=y
    · subst y
      simp only [PositionalArrivalMarginals.observedCells,Finset.mem_filter,
        Finset.mem_univ,true_and,ite_true]
    · have hval : x.val≠y.val := fun h ↦ hxy (Subtype.ext h)
      simp only [PositionalArrivalMarginals.observedCells,Finset.mem_filter,
        Finset.mem_univ,true_and,hval,hxy,ite_false]
  · apply Finset.sum_congr rfl
    intro e _he
    by_cases hx : x.val∈e.val <;> by_cases hy : y.val∈e.val <;>
      simp only [PositionalArrivalMarginals.observedCells,Finset.mem_filter,
        Finset.mem_univ,hx,hy,and_self,and_false,false_and,ite_true,ite_false]

theorem covariance_coordinates {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x y : G) :
    cov[coordinate G E X x,coordinate G E X y;P] =
      (if x=y then p x.val-PaperP1.PositionalCompoundPoisson.incidence E q x.val else 0)+
        ∑ e∈E,if x.val∈e ∧ y.val∈e then q e else 0 := by
  rw [coordinate_eq_sum G E X x,coordinate_eq_sum G E X y,
    covariance_selected_sums P _ X hX hInd]
  have hi := sum_observed_inter G E
    (fun a ↦ (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a : ℝ)) x y
  have hleft (z : G) :
      (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq (Sum.inl z) : ℝ)=
        p z.val-PaperP1.PositionalCompoundPoisson.incidence E q z.val := rfl
  have hright (e : E) :
      (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq (Sum.inr e) : ℝ)=q e.val := rfl
  simp only [hleft,hright] at hi
  rw [Finset.sum_coe_sort E (fun e ↦ if x.val∈e ∧ y.val∈e then q e else 0)] at hi
  convert hi using 1
  apply Finset.sum_congr
  · ext a
    simp only [Finset.mem_inter]
  · intro a _ha
    rfl

theorem mean_coordinate {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x : G) :
    Integrable (coordinate G E X x) P ∧ (∫ ω,coordinate G E X x ω ∂P)=p x.val := by
  obtain ⟨r,hr,hLaw⟩ :=
    PositionalArrivalMarginals.hasLaw_coordinate G E p q hp hq P X hX hInd x
  unfold coordinate
  exact ⟨(mean_of_hasLaw P _ r hLaw).1,(mean_of_hasLaw P _ r hLaw).2.trans hr⟩

theorem memLp_coordinate {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x : G) : MemLp (coordinate G E X x) 2 P := by
  obtain ⟨r,_hr,hLaw⟩ :=
    PositionalArrivalMarginals.hasLaw_coordinate G E p q hp hq P X hX hInd x
  exact memLp_two_of_hasLaw P _ r hLaw

theorem variance_coordinate {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x : G) : Var[coordinate G E X x;P]=p x.val := by
  obtain ⟨r,hr,hLaw⟩ :=
    PositionalArrivalMarginals.hasLaw_coordinate G E p q hp hq P X hX hInd x
  unfold coordinate
  exact (variance_of_hasLaw P _ r hLaw).trans hr

theorem pair_eq_of_card_two {ι : Type*} (e : Finset ι) (x y : ι)
    (hcard : e.card=2) (hxy : x≠y) : (x∈e ∧ y∈e) ↔ e={x,y} := by
  classical
  constructor
  · intro h
    have hsub : ({x,y} : Finset ι) ⊆ e := by
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with hx|hy
      · simpa only [hx] using h.1
      · simpa only [hy] using h.2
    exact (Finset.eq_of_subset_of_card_le hsub
      (by rw [hcard,Finset.card_pair hxy])).symm
  · rintro rfl
    simp only [Finset.mem_insert,Finset.mem_singleton,eq_self,or_true,true_or,and_self]

theorem covariance_pairs {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x y : G) (hxy : x≠y) :
    cov[coordinate G E X x,coordinate G E X y;P] =
      if {x.val,y.val}∈E then q {x.val,y.val} else 0 := by
  rw [covariance_coordinates G E p q hp hq P X hX hInd x y,ite_eq_right hxy,zero_add]
  have hval : x.val≠y.val := fun h ↦ hxy (Subtype.ext h)
  calc
    (∑ e∈E,if x.val∈e ∧ y.val∈e then q e else 0) =
        ∑ e∈E,if e={x.val,y.val} then q e else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [pair_eq_of_card_two e x.val y.val (hE e he) hval]
    _ = _ := by rw [Finset.sum_ite_eq']

theorem covariance_pair_matrix {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x y : G) :
    cov[coordinate G E X x,coordinate G E X y;P] =
      if x=y then p x.val else
        if {x.val,y.val}∈E then q {x.val,y.val} else 0 := by
  by_cases hxy : x=y
  · subst y
    rw [ite_eq_left rfl,
      covariance_self (memLp_coordinate G E p q hp hq P X hX hInd x).aemeasurable]
    exact variance_coordinate G E p q hp hq P X hX hInd x
  · rw [ite_eq_right hxy]
    exact covariance_pairs G E p q hp hq hE P X hX hInd x y hxy

theorem covariance_canonical {ι : Type*}
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (x y : G) :
    cov[coordinate G E (fun a ω ↦ ω a) x,coordinate G E (fun a ω ↦ ω a) y;
      (PaperP1.PositionalPoissonRealization.poissonProduct
        (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq)).val] =
      (if x=y then p x.val-PaperP1.PositionalCompoundPoisson.incidence E q x.val else 0)+
        ∑ e∈E,if x.val∈e ∧ y.val∈e then q e else 0 :=
  covariance_coordinates G E p q hp hq _ _
    (PaperP1.PositionalPoissonRealization.poissonProduct_hasLaw_eval _)
    (PaperP1.PositionalPoissonRealization.poissonProduct_independent _) x y

theorem covariance_canonical_pairs {ι : Type*}
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (hE : ∀ e∈E,e.card=2) (x y : G) :
    cov[coordinate G E (fun a ω ↦ ω a) x,coordinate G E (fun a ω ↦ ω a) y;
      (PaperP1.PositionalPoissonRealization.poissonProduct
        (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq)).val] =
      if x=y then p x.val else
        if {x.val,y.val}∈E then q {x.val,y.val} else 0 :=
  covariance_pair_matrix G E p q hp hq hE _ _
    (PaperP1.PositionalPoissonRealization.poissonProduct_hasLaw_eval _)
    (PaperP1.PositionalPoissonRealization.poissonProduct_independent _) x y

end PaperP1.PositionalArrivalCovariance
