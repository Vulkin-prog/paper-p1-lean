module

public import PaperP1.Probability.PositionalProbabilityMeasure
public import PaperP1.Probability.PositionalCompoundPoisson
public import PaperP1.Probability.PositionalGrid
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic

/-! # Independent Poisson variables realizing the exact positional target

The finite product space constructs the arrivals. Any independent realization
has the same completed-law measure, including its original-grid event masses.
The weighted arithmetic application is in `IndependentPositionalApproximation`.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.PositionalPoissonRealization

open MeasureTheory ProbabilityTheory PaperP1.PositionalFiniteLaw
  PaperP1.CompletedPositionalLaw PaperP1.PositivePositionalConvolution
  PaperP1.FiniteConvolutionAlgebra PaperP1.PositionalCoefficientExpansion
open scoped NNReal

local instance realizationDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {ι : Type*}

theorem coeff_atom_mul (u w : Configuration ι) (κ : Space ι) :
    coeff w (ofFinite (atom u)*κ)=∑' v : Configuration ι, if u+v=w then coeff v κ else 0 := by
  have hh := (HasSum.mul_left (ofFinite (atom u)) (hasSum_coeff_atoms κ)).map (coeff w) (coeff w).continuous
  rw [← hh.tsum_eq]
  apply tsum_congr
  intro v
  dsimp only [Function.comp_def]
  rw [mul_smul_comm,map_smul,← map_mul,atom_mul,coeff_ofFinite]
  simp only [atom,AddMonoidAlgebra.coeff_single,Finsupp.single_apply,smul_eq_mul]
  split_ifs <;> simp_all

theorem coeff_mul (ν κ : Space ι) (w : Configuration ι) :
    coeff w (ν*κ)=∑' u : Configuration ι, ∑' v : Configuration ι,
      if u+v=w then coeff u ν*coeff v κ else 0 := by
  have hh := (HasSum.mul_right κ (hasSum_coeff_atoms ν)).map (coeff w) (coeff w).continuous
  rw [← hh.tsum_eq]
  apply tsum_congr
  intro u
  dsimp only [Function.comp_def]
  rw [smul_mul_assoc,map_smul,smul_eq_mul,coeff_atom_mul,← tsum_mul_left]
  apply tsum_congr
  intro v
  split_ifs <;> simp_all

theorem one_probability : IsProbability (1 : Space ι) :=
  ⟨coeff_one_nonneg,PaperP1.PositionalTotalMass.totalMass_one⟩

def channelJump (G : Finset ι) (E : Finset (Finset ι)) : ↥G ⊕ ↥E → Configuration ι
  | Sum.inl x => direction x.val
  | Sum.inr e => ∑ x ∈ e.val, direction x

def channelRate (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G, 0≤p x-PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E, 0≤q e) : ↥G ⊕ ↥E → ℝ≥0
  | Sum.inl x => ⟨p x.val-PositionalCompoundPoisson.incidence E q x.val,hp x.val x.property⟩
  | Sum.inr e => ⟨q e.val,hq e.val e.property⟩

theorem field_coordinate (G : Finset ι) (E : Finset (Finset ι))
    (ω : (↥G ⊕ ↥E) → ℕ) (x : G) :
    (∑ a : ↥G ⊕ ↥E, ω a • channelJump G E a) x.val =
      ω (Sum.inl x) + ∑ e : E, if x.val ∈ e.val then ω (Sum.inr e) else 0 := by
  classical
  rw [Fintype.sum_sum_type, Finsupp.add_apply]
  congr 1
  · have hsingle (y : G) : (ω (Sum.inl y) • direction y.val) x.val =
        if y = x then ω (Sum.inl y) else 0 := by
      by_cases hy : y = x
      · subst y
        simp [direction]
      · have hxy : y.val ≠ x.val := fun h ↦ hy (Subtype.ext h)
        simp [direction, hxy, hy]
    change (∑ y : G, ω (Sum.inl y) • direction y.val) x.val = _
    rw [Finset.sum_apply']
    simp only [hsingle, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · simp [channelJump, Finset.sum_apply', Finsupp.smul_apply, direction,
      Finsupp.single_apply]

theorem channel_product (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G, 0≤p x-PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E, 0≤q e) :
    (∏ a : ↥G ⊕ ↥E, PositionalPoissonJump.jump (channelJump G E a) (channelRate G E p q hp hq a : ℝ))=
      PositionalCompoundPoisson.target G E p q := by
  rw [Fintype.prod_sum_type]
  change (∏ x : G, PositionalPoissonJump.jump (direction x.val)
      (p x.val-PositionalCompoundPoisson.incidence E q x.val))*
    (∏ e : E, PositionalPoissonJump.jump (∑ x ∈ e.val, direction x) (q e.val))=_
  rw [Finset.prod_coe_sort G (fun x ↦ PositionalPoissonJump.jump (direction x)
      (p x-PositionalCompoundPoisson.incidence E q x)),
    Finset.prod_coe_sort E (fun e ↦ PositionalPoissonJump.jump (∑ x ∈ e, direction x) (q e))]
  rfl

variable [Countable (Configuration ι)] [MeasurableSpace (Configuration ι)]
  [MeasurableSingletonClass (Configuration ι)]

local instance realizationMeasurableAdd : MeasurableAdd₂ (Configuration ι) :=
  ⟨Measurable.of_discrete⟩

def poissonJumpLaw (m : Configuration ι) (μ : ℝ≥0) : ProbabilityMeasure (Configuration ι) :=
  ⟨(poissonMeasure μ).map (fun n : ℕ ↦ n • m),by infer_instance⟩

omit [Countable (Configuration ι)] in
theorem poissonJumpLaw_real_singleton (m v : Configuration ι) (μ : ℝ≥0) :
    (poissonJumpLaw m μ : Measure (Configuration ι)).real {v}=
      ∑' n : ℕ, if n • m=v then PoissonSequence.mass (μ : ℝ) n else 0 := by
  change ((poissonMeasure μ).map (fun n : ℕ ↦ n • m)).real {v}=_
  rw [map_measureReal_apply Measurable.of_discrete (measurableSet_singleton v)]
  rw [← integral_indicator_one ((Set.to_countable _).measurableSet)]
  rw [integral_poissonMeasure]
  apply tsum_congr
  intro n
  simp only [Set.indicator_apply,Set.mem_preimage,Set.mem_singleton_iff,Pi.one_apply,
    PoissonSequence.mass]
  split_ifs <;> simp_all

theorem law_jump (m : Configuration ι) (μ : ℝ≥0) :
    PositionalProbabilityMeasure.law (PositionalPoissonJump.jump m (μ : ℝ))
      (jump_isProbability m (μ : ℝ) μ.property)=poissonJumpLaw m μ := by
  apply PositionalProbabilityMeasure.law_eq_of_singletons
  intro v
  rw [poissonJumpLaw_real_singleton,PositionalPoissonJump.coeff_jump]

theorem integral_law (ν : Space ι) (hν : IsProbability ν) (f : Configuration ι → ℝ) :
    (∫ v, f v ∂(PositionalProbabilityMeasure.law ν hν : Measure (Configuration ι)))=
      ∑' v : Configuration ι, coeff v ν*f v := by
  change (∫ v, f v ∂Measure.sum (fun v ↦ ENNReal.ofReal (coeff v ν) • Measure.dirac v))=_
  rw [integral_sum_dirac (by simp)]
  simp only [ENNReal.toReal_ofReal (hν.1 _),smul_eq_mul]

theorem law_mul (ν κ : Space ι) (hν : IsProbability ν) (hκ : IsProbability κ) :
    (PositionalProbabilityMeasure.law (ν*κ) (mul_isProbability hν hκ) : Measure (Configuration ι))=
      Measure.conv (PositionalProbabilityMeasure.law ν hν) (PositionalProbabilityMeasure.law κ hκ) := by
  apply Measure.ext_of_measureReal_singleton
  intro w
  rw [PositionalProbabilityMeasure.real_singleton,coeff_mul]
  symm
  unfold Measure.conv
  rw [map_measureReal_apply Measurable.of_discrete (measurableSet_singleton w)]
  let S : Set (Configuration ι × Configuration ι) := {p | p.1+p.2=w}
  have hS : MeasurableSet S := (Set.to_countable _).measurableSet
  change ((PositionalProbabilityMeasure.law ν hν : Measure (Configuration ι)).prod
    (PositionalProbabilityMeasure.law κ hκ : Measure (Configuration ι))).real S=_
  rw [← integral_indicator_one hS]
  have hI : Integrable (S.indicator (1 : Configuration ι × Configuration ι → ℝ))
      ((PositionalProbabilityMeasure.law ν hν : Measure (Configuration ι)).prod
        (PositionalProbabilityMeasure.law κ hκ : Measure (Configuration ι))) :=
    (integrable_const (1 : ℝ)).indicator hS
  rw [integral_prod _ hI,integral_law]
  apply tsum_congr
  intro u
  rw [integral_law,← tsum_mul_left]
  apply tsum_congr
  intro v
  simp only [S,Set.indicator_apply,Set.mem_ofPred_eq,Pi.one_apply]
  split_ifs <;> simp_all

theorem law_one (h : IsProbability (1 : Space ι)) :
    (PositionalProbabilityMeasure.law (1 : Space ι) h : Measure (Configuration ι))=Measure.dirac 0 := by
  apply Measure.ext_of_measureReal_singleton
  intro v
  rw [PositionalProbabilityMeasure.real_singleton,
    ← map_one (ofFinite : FieldLaw ι →+* Space ι),coeff_ofFinite]
  simp [AddMonoidAlgebra.one_def,AddMonoidAlgebra.coeff_single,Finsupp.single_apply,
    Measure.real,Pi.single_apply,apply_ite,eq_comm]

theorem hasLaw_finite_sum {α Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Finset α) (ν : α → Space ι) (hν : ∀ a, IsProbability (ν a))
    (X : α → Ω → Configuration ι)
    (hX : ∀ a, HasLaw (X a) (PositionalProbabilityMeasure.law (ν a) (hν a)) P)
    (hInd : iIndepFun X P) :
    HasLaw (fun ω ↦ ∑ a ∈ S, X a ω)
      (PositionalProbabilityMeasure.law (∏ a ∈ S, ν a)
        (prod_isProbability S ν (fun a _ha ↦ hν a))) P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty,Finset.prod_empty,law_one]
    exact ⟨measurable_const.aemeasurable,by simp⟩
  | @insert a S ha ih =>
    have hAS := (hInd.indepFun_finsetSum_of_notMem₀ (fun a ↦ (hX a).aemeasurable) ha).symm
    have hsum : (∑ j ∈ S, X j)=(fun ω ↦ ∑ j ∈ S, X j ω) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [hsum] at hAS
    have hh := hAS.hasLaw_fun_add (hX a) ih
    simpa only [Finset.sum_insert ha,Finset.prod_insert ha,← law_mul,Finset.sum_apply] using hh

theorem hasLaw_poisson_jump {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℕ) (m : Configuration ι) (μ : ℝ≥0) (hX : HasLaw X (poissonMeasure μ) P) :
    HasLaw (fun ω ↦ X ω • m)
      (PositionalProbabilityMeasure.law (PositionalPoissonJump.jump m (μ : ℝ))
        (jump_isProbability m (μ : ℝ) μ.property)) P := by
  rw [law_jump]
  have hmap : HasLaw (fun n : ℕ ↦ n • m) (poissonJumpLaw m μ) (poissonMeasure μ) :=
    hasLaw_map Measurable.of_discrete.aemeasurable
  exact hmap.fun_comp hX

def poissonProduct {α : Type*} [Fintype α] (μ : α → ℝ≥0) : ProbabilityMeasure (α → ℕ) :=
  ⟨Measure.pi (fun a ↦ poissonMeasure (μ a)), by infer_instance⟩

theorem poissonProduct_hasLaw_eval {α : Type*} [Fintype α] (μ : α → ℝ≥0) (a : α) :
    HasLaw (fun ω : α → ℕ ↦ ω a) (poissonMeasure (μ a)) (poissonProduct μ) :=
  (measurePreserving_eval (fun a ↦ poissonMeasure (μ a)) a).hasLaw

theorem poissonProduct_independent {α : Type*} [Fintype α] (μ : α → ℝ≥0) :
    iIndepFun (fun a (ω : α → ℕ) ↦ ω a) (poissonProduct μ) :=
  iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)

theorem hasLaw_independent_poisson_sum {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Finset α)
    (m : α → Configuration ι) (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a, HasLaw (X a) (poissonMeasure (μ a)) P) (hInd : iIndepFun X P) :
    HasLaw (fun ω ↦ ∑ a ∈ S, X a ω • m a)
      (PositionalProbabilityMeasure.law (∏ a ∈ S, PositionalPoissonJump.jump (m a) (μ a : ℝ))
        (prod_isProbability S _ (fun a _ha ↦ jump_isProbability (m a) (μ a : ℝ) (μ a).property))) P := by
  have hY := hInd.comp (fun a (n : ℕ) ↦ n • m a) (fun _a ↦ Measurable.of_discrete)
  exact hasLaw_finite_sum P S (fun a ↦ PositionalPoissonJump.jump (m a) (μ a : ℝ))
    (fun a ↦ jump_isProbability (m a) (μ a : ℝ) (μ a).property)
    (fun a ω ↦ X a ω • m a) (fun a ↦ hasLaw_poisson_jump P (X a) (m a) (μ a) (hX a)) hY

theorem hasLaw_single_pair_field (G : Finset ι) (E : Finset (Finset ι))
    (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G, 0≤p x-PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E, 0≤q e) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a, HasLaw (X a) (poissonMeasure (channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) :
    HasLaw (fun ω ↦ ∑ a : ↥G ⊕ ↥E, X a ω • channelJump G E a)
      (PositionalProbabilityMeasure.law (PositionalCompoundPoisson.target G E p q)
        (PositionalCompoundPoisson.target_isProbability G E p q hp hq)) P := by
  have h := hasLaw_independent_poisson_sum P Finset.univ (channelJump G E)
    (channelRate G E p q hp hq) X hX hInd
  simpa only [channel_product] using h

theorem grid_probability_of_hasLaw (G : Finset ι) (ν : Space ι) (hν : IsProbability ν)
    (hG : PositionalGroundSupport.Supported G ν) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Configuration ι)
    (hX : HasLaw X (PositionalProbabilityMeasure.law ν hν) P) (z : G → ℕ) :
    P.real {ω | ∀ x : G, X ω x.val=z x}=coeff (PositionalGrid.encode G z) ν := by
  let B : Set (Configuration ι) := {v | ∀ x : G, v x.val=z x}
  have hB : MeasurableSet B := (Set.to_countable _).measurableSet
  have hmeasure : P.real {ω | ∀ x : G, X ω x.val=z x}=
      (PositionalProbabilityMeasure.law ν hν : Measure (Configuration ι)).real B :=
    hX.measureReal_eq (p:=fun v ↦ ∀ x : G, v x.val=z x) hB
  rw [hmeasure,← integral_indicator_one hB,integral_law]
  have hpoint (v : Configuration ι) : coeff v ν*(B.indicator (1 : Configuration ι → ℝ) v)=
      if v=PositionalGrid.encode G z then coeff v ν else 0 := by
    by_cases hg : PositionalGroundSupport.OnGround G v
    · have heq : (∀ x : G, v x.val=z x) ↔ v=PositionalGrid.encode G z := by
        constructor
        · intro hx
          have hfun : (fun x : G ↦ v x.val)=z := funext hx
          rw [← hfun,PositionalGrid.encode_restrict G v hg]
        · intro hv
          subst v
          exact fun x ↦ PositionalGrid.encode_apply_mem G z x
      simp only [B,Set.indicator_apply,Set.mem_ofPred_eq,Pi.one_apply,heq,mul_ite,mul_one,mul_zero]
    · simp only [hG v hg,zero_mul,ite_self]
  calc
    _ = ∑' v : Configuration ι, if v=PositionalGrid.encode G z then coeff v ν else 0 :=
      tsum_congr hpoint
    _ = _ := by simp only [tsum_ite_eq]

theorem hasLaw_canonical_single_pair_field (G : Finset ι) (E : Finset (Finset ι))
    (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G, 0≤p x-PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E, 0≤q e) :
    HasLaw (fun ω : (↥G ⊕ ↥E) → ℕ ↦ ∑ a : ↥G ⊕ ↥E, ω a • channelJump G E a)
      (PositionalProbabilityMeasure.law (PositionalCompoundPoisson.target G E p q)
        (PositionalCompoundPoisson.target_isProbability G E p q hp hq))
      (poissonProduct (channelRate G E p q hp hq)) :=
  hasLaw_single_pair_field G E p q hp hq _ _
    (poissonProduct_hasLaw_eval _) (poissonProduct_independent _)

end PaperP1.PositionalPoissonRealization
