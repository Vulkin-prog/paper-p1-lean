module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Basic
public import PaperP1.Probability.PositionalPoissonRealization
public import PaperP1.Probability.PoissonFactorialMoments

/-! # Exact marginal laws and factorial moments of compensated arrival fields

Each site has its original Poisson intensity for every finite packet family.
The actual factorial tests are integrable in every independent realization.
No countability of the ambient configuration space is required.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.PositionalArrivalMarginals

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal

local instance marginalDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem poisson_zero : poissonMeasure (0 : ℝ≥0) = Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_measureReal_singleton
  intro n
  rw [poissonMeasure_real_singleton]
  cases n <;> simp [Measure.real]

theorem hasLaw_sum {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Finset α)
    (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a, HasLaw (X a) (poissonMeasure (μ a)) P) (hInd : iIndepFun X P) :
    HasLaw (fun ω ↦ ∑ a ∈ S, X a ω) (poissonMeasure (∑ a ∈ S, μ a)) P := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty,poisson_zero]
    exact ⟨measurable_const.aemeasurable,by simp⟩
  | @insert a S ha ih =>
    have hAS := (hInd.indepFun_finsetSum_of_notMem₀ (fun a ↦ (hX a).aemeasurable) ha).symm
    have hsum : (∑ j∈S,X j)=(fun ω ↦ ∑ j∈S,X j ω) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [hsum] at hAS
    have hh := hAS.hasLaw_add_poissonMeasure (hX a) ih
    have hadd : (X a + fun ω ↦ ∑ j ∈ S,X j ω) =
        (fun ω ↦ X a ω + ∑ j ∈ S,X j ω) := by
      funext ω
      rfl
    rw [hadd] at hh
    simpa only [Finset.sum_insert ha] using hh

theorem hasLaw_selected_sum {α Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Finset α) (b : α → Prop)
    (μ : α → ℝ≥0) (X : α → Ω → ℕ)
    (hX : ∀ a, HasLaw (X a) (poissonMeasure (μ a)) P) (hInd : iIndepFun X P) :
    HasLaw (fun ω ↦ ∑ a ∈ S, if b a then X a ω else 0)
      (poissonMeasure (∑ a ∈ S, if b a then μ a else 0)) P := by
  simpa only [Finset.sum_filter] using hasLaw_sum P (S.filter b) μ X hX hInd

def observedCells {ι : Type*} (G : Finset ι) (E : Finset (Finset ι)) (x : ι) :
    Finset (↥G ⊕ ↥E) :=
  univ.filter fun a ↦ match a with
    | Sum.inl y => y.val=x
    | Sum.inr e => x∈e.val

theorem sum_observed {ι M : Type*} [AddCommMonoid M]
    (G : Finset ι) (E : Finset (Finset ι)) (w : (↥G ⊕ ↥E) → M) (x : G) :
    (∑ a ∈ observedCells G E x.val,w a) =
      w (Sum.inl x)+∑ e : E,if x.val∈e.val then w (Sum.inr e) else 0 := by
  rw [observedCells,Finset.sum_filter,Fintype.sum_sum_type]
  congr 1
  · have hs (y : G) : (if y.val=x.val then w (Sum.inl y) else 0) =
        if y=x then w (Sum.inl y) else 0 := by
      by_cases hy : y=x
      · subst y
        simp only [ite_true]
      · have hval : y.val≠x.val := fun h ↦ hy (Subtype.ext h)
        simp only [hval,hy,ite_false]
    simp only [hs,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  · apply Finset.sum_congr rfl
    intro e _he
    by_cases hx : x.val∈e.val
    · simp only [hx,ite_true]
    · simp only [hx,ite_false]

theorem coordinate_sum {ι : Type*} (G : Finset ι) (E : Finset (Finset ι))
    (w : (↥G ⊕ ↥E) → ℕ) (x : G) :
    (∑ a : ↥G ⊕ ↥E,w a • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val =
      ∑ a ∈ observedCells G E x.val,w a := by
  rw [PaperP1.PositionalPoissonRealization.field_coordinate,sum_observed]

theorem rate_sum_observed {ι : Type*} (G : Finset ι) (E : Finset (Finset ι))
    (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (x : G) :
    ((∑ a ∈ observedCells G E x.val,
      PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a : ℝ≥0) : ℝ)=p x.val := by
  rw [NNReal.coe_sum,sum_observed]
  have hleft (y : G) :
      (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq (Sum.inl y) : ℝ)=
        p y.val-PaperP1.PositionalCompoundPoisson.incidence E q y.val := rfl
  have hright (e : E) :
      (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq (Sum.inr e) : ℝ)=q e.val := rfl
  simp only [hleft,hright]
  have hi : (∑ e : E,if x.val∈e.val then q e.val else 0)=
      PaperP1.PositionalCompoundPoisson.incidence E q x.val := by
    rw [Finset.sum_coe_sort E (fun e ↦ if x.val∈e then q e else 0)]
    unfold PaperP1.PositionalCompoundPoisson.incidence
    apply Finset.sum_congr rfl
    intro e _he
    by_cases hx : x.val∈e
    · simp only [hx,ite_true]
    · simp only [hx,ite_false]
  rw [hi]
  exact sub_add_cancel _ _

theorem hasLaw_coordinate {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x : G) :
    ∃ r : ℝ≥0,(r : ℝ)=p x.val ∧
      HasLaw (fun ω ↦ (∑ a : ↥G ⊕ ↥E,
          X a ω • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val)
        (poissonMeasure r) P := by
  let r : ℝ≥0 := ∑ a ∈ observedCells G E x.val,
    PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a
  refine ⟨r,rate_sum_observed G E p q hp hq x,?_⟩
  have h := hasLaw_sum P (observedCells G E x.val)
    (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq) X hX hInd
  have heq : (fun ω ↦ (∑ a : ↥G ⊕ ↥E,
        X a ω • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val)=
      (fun ω ↦ ∑ a ∈ observedCells G E x.val,X a ω) := by
    funext ω
    exact coordinate_sum G E (fun a ↦ X a ω) x
  rw [heq]
  exact h

theorem hasLaw_canonical_coordinate {ι : Type*}
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (x : G) :
    ∃ r : ℝ≥0,(r : ℝ)=p x.val ∧
      HasLaw (fun ω : (↥G ⊕ ↥E) → ℕ ↦ (∑ a : ↥G ⊕ ↥E,
          ω a • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val)
        (poissonMeasure r)
        (PaperP1.PositionalPoissonRealization.poissonProduct
          (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq)).val :=
  hasLaw_coordinate G E p q hp hq _ _
    (PaperP1.PositionalPoissonRealization.poissonProduct_hasLaw_eval _)
    (PaperP1.PositionalPoissonRealization.poissonProduct_independent _) x

theorem integrable_poisson_factorial (r : ℝ≥0) (j : ℕ) :
    Integrable (fun n : ℕ ↦ (n.descFactorial j : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hnorm (n : ℕ) : ‖(n.descFactorial j : ℝ)‖=(n.descFactorial j : ℝ) :=
    Real.norm_of_nonneg (Nat.cast_nonneg _)
  simpa only [hnorm,PaperP1.PoissonSequence.mass] using
    (PaperP1.PoissonFactorialMoments.hasSum_mass_factorial (r : ℝ) r.property j).summable

theorem integral_poisson_factorial (r : ℝ≥0) (j : ℕ) :
    (∫ n : ℕ,(n.descFactorial j : ℝ) ∂poissonMeasure r)=(r : ℝ)^j := by
  rw [integral_poissonMeasure]
  simpa only [PaperP1.PoissonSequence.mass,smul_eq_mul] using
    (PaperP1.PoissonFactorialMoments.hasSum_mass_factorial (r : ℝ) r.property j).tsum_eq

theorem factorial_moment_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℕ) (r : ℝ≥0) (hY : HasLaw Y (poissonMeasure r) P) (j : ℕ) :
    Integrable (fun ω ↦ ((Y ω).descFactorial j : ℝ)) P ∧
      (∫ ω,((Y ω).descFactorial j : ℝ) ∂P)=(r : ℝ)^j := by
  refine ⟨hY.integrable_comp (integrable_poisson_factorial r j),?_⟩
  have h := hY.integral_comp
    (show AEStronglyMeasurable (fun n : ℕ ↦ (n.descFactorial j : ℝ)) (poissonMeasure r) from
      Measurable.of_discrete.aestronglyMeasurable)
  exact h.trans (integral_poisson_factorial r j)

theorem coordinate_factorial_moment {ι Ω : Type*} [MeasurableSpace Ω]
    (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (↥G ⊕ ↥E) → Ω → ℕ)
    (hX : ∀ a,HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate G E p q hp hq a)) P)
    (hInd : iIndepFun X P) (x : G) (j : ℕ) :
    let Z := fun ω ↦ (∑ a : ↥G ⊕ ↥E,
      X a ω • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val
    Integrable (fun ω ↦ ((Z ω).descFactorial j : ℝ)) P ∧
      (∫ ω,((Z ω).descFactorial j : ℝ) ∂P)=(p x.val)^j := by
  obtain ⟨r,hr,hLaw⟩ := hasLaw_coordinate G E p q hp hq P X hX hInd x
  have h := factorial_moment_of_hasLaw P _ r hLaw j
  simpa only [hr] using h

end PaperP1.PositionalArrivalMarginals
