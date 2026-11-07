module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Ring.Basic
public import PaperP1.Probability.StoppedMeasureLaw

/-! # Exact expansions for dependent indicator counts
Every source count, probability and heterogeneous centered moment is literal.
The ordered boundary deletes the greatest element of its prefix. The positive
kernel keeps the actual dependent suffix and is charged only in ordinary l1.
No independence or approximation assumption is imposed.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1Registry.DependentExpansion
open Finset MeasureTheory
open scoped Classical BigOperators

variable {ι Ω : Type*}

/-- Prefix with the greatest element removed, also defined on the empty set. -/
def properPrefix [LinearOrder ι] (I : Finset ι) : Finset ι :=
  I.filter fun x ↦ ∃ y ∈ I, x<y

def Hereditary (D : Finset ι → Prop) : Prop :=
  ∀ ⦃I J⦄, J ⊆ I → D I → D J

def Boundary [LinearOrder ι] (D : Finset ι → Prop) (I : Finset ι) : Prop :=
  ¬ D I ∧ D (properPrefix I)

def suffix [LinearOrder ι] (G I : Finset ι) : Finset ι :=
  G.filter fun y ↦ ∀ x ∈ I, x<y

def retained (G : Finset ι) (D : Finset ι → Prop) : Finset (Finset ι) :=
  G.powerset.filter D

def boundary [LinearOrder ι] (G : Finset ι) (D : Finset ι → Prop) : Finset (Finset ι) :=
  G.powerset.filter (Boundary D)

abbrev SignedLaw := AddMonoidAlgebra ℝ ℕ

def scalar (r : ℝ) : SignedLaw := AddMonoidAlgebra.single 0 r

def atom (k : ℕ) : SignedLaw := AddMonoidAlgebra.single k 1

def difference : SignedLaw := atom 1-atom 0

def bernoulli (p : ℝ) : SignedLaw := atom 0+scalar p*difference

/-- Ordinary unweighted singleton l1 norm. -/
def l1Norm (ν : SignedLaw) : ℝ := ν.coeff.sum fun _ r ↦ |r|

def totalMass (ν : SignedLaw) : ℝ := ν.coeff.sum fun _ r ↦ r

def indicator (b : Bool) : ℝ := if b then 1 else 0

def count (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) : ℕ :=
  ∑ x ∈ G, (J x ω).toNat

/-- All count probabilities, represented on their literal finite support. -/
def countLaw [MeasurableSpace Ω] (G : Finset ι) (μ : Measure Ω)
    (J : ι → Ω → Bool) : SignedLaw :=
  ∑ k ∈ range (G.card+1), AddMonoidAlgebra.single k (μ.real {ω | count G J ω=k})

def jointMoment [MeasurableSpace Ω] (μ : Measure Ω) (J : ι → Ω → Bool)
    (I : Finset ι) : ℝ := ∫ ω, ∏ x ∈ I, indicator (J x ω) ∂μ

def marginal [MeasurableSpace Ω] (μ : Measure Ω) (J : ι → Ω → Bool) (x : ι) : ℝ :=
  ∫ ω, indicator (J x ω) ∂μ

def centeredMoment [MeasurableSpace Ω] (μ : Measure Ω) (J : ι → Ω → Bool)
    (I : Finset ι) : ℝ :=
  ∫ ω, ∏ x ∈ I, (indicator (J x ω)-marginal μ J x) ∂μ

/-- A signed reference of mass one, whose coefficients need not be positive. -/
def retainedReference [MeasurableSpace Ω] (G : Finset ι) (D : Finset ι → Prop)
    (μ : Measure Ω) (J : ι → Ω → Bool) : SignedLaw :=
  ∑ I ∈ retained G D, scalar (jointMoment μ J I)*difference^I.card


/-- Finite reconstruction uses the literal coefficient sequence. -/
theorem reconstruct (ν : SignedLaw) (n : ℕ)
    (hν : ∀ k, n<k → ν.coeff k=0) :
    ν=∑ k ∈ range (n+1), AddMonoidAlgebra.single k (ν.coeff k) := by
  classical
  have hs : ν.coeff.support ⊆ range (n+1) := by
    intro k hk
    apply mem_range.mpr
    by_contra h
    have hz := hν k (by omega)
    exact (Finsupp.mem_support_iff.mp hk) hz
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single ν]
  exact Finsupp.sum_of_support_subset _ hs _ (fun _ _ ↦ by simp)

theorem countLaw_eq_source [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    countLaw G μ J=PaperP1.Probability.observedCountLaw G μ J hJ := by
  have h := reconstruct (PaperP1.Probability.observedCountLaw G μ J hJ) G.card
    (fun k hk ↦ PaperP1.Probability.countLaw_coeff_eq_zero_of_card_lt G
      (PaperP1.Probability.indicatorObservationProbability μ J hJ).weight
      (fun x σ ↦ σ x) hk)
  rw [h]
  unfold countLaw
  apply Finset.sum_congr rfl
  intro k _
  rw [PaperP1.Probability.observedCountLaw_coeff]
  rfl

theorem totalMass_eq_source (ν : SignedLaw) :
    totalMass ν=PaperP1.Probability.totalMass ν :=
  (PaperP1.Probability.totalMass_eq_sum_coeff ν).symm

theorem l1Norm_eq_source (ν : SignedLaw) :
    l1Norm ν=PaperP1.Probability.l1Norm ν := rfl

theorem retainedReference_eq_source [MeasurableSpace Ω]
    (G : Finset ι) (D : Finset ι → Prop) (μ : Measure Ω)
    (J : ι → Ω → Bool) :
    retainedReference G D μ J=PaperP1.Probability.measureRetainedReference G D μ J := rfl

theorem jointMoment_eq_source [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ι → Ω → Bool) (I : Finset ι) :
    jointMoment μ J I=PaperP1.Probability.measureJointMoment μ J I := rfl

theorem marginal_eq_source [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ι → Ω → Bool) (x : ι) :
    marginal μ J x=PaperP1.Probability.measureMarginal μ J x := rfl

theorem centeredMoment_eq_source [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ι → Ω → Bool) (I : Finset ι) :
    centeredMoment μ J I=PaperP1.Probability.measureCenteredMoment μ J
      (PaperP1.Probability.measureMarginal μ J) I := rfl

theorem boundary_eq_source [LinearOrder ι] (G : Finset ι) (D : Finset ι → Prop) :
    boundary G D=PaperP1.Algebra.boundarySets G D := rfl

/-- Exact first-excluded-prefix identity, already over a commutative semiring. -/
theorem polynomial_expansion {R : Type*} [LinearOrder ι] [CommSemiring R]
    (G : Finset ι) (D : Finset ι → Prop) (u : ι → R) (t : R)
    (hD : Hereditary D) (h0 : D ∅) :
    (∏ x ∈ G, (1+t*u x))=
      (∑ I ∈ retained G D, t^I.card*∏ x ∈ I, u x)+
      ∑ I ∈ boundary G D, (t^I.card*∏ x ∈ I, u x)*
        ∏ y ∈ suffix G I, (1+t*u y) :=
by
  exact PaperP1.Algebra.stopped_expansion G D u t hD h0

/-- The exact actual law, with heterogeneous marginals and arbitrary dependence.
Its coefficients are the original count probabilities and it is normalized. -/
theorem centered_identity [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    (∀ k, (countLaw G μ J).coeff k=μ.real {ω | count G J ω=k}) ∧
    (∀ k, 0 ≤ (countLaw G μ J).coeff k) ∧ totalMass (countLaw G μ J)=1 ∧
    countLaw G μ J=∑ I ∈ G.powerset, scalar (centeredMoment μ J I)*
      difference^I.card*∏ x ∈ G \ I, bernoulli (marginal μ J x) :=
by
  rw [countLaw_eq_source G μ J hJ]
  have hp := PaperP1.Probability.observedCountLaw_isProbability G μ J hJ
  refine ⟨?_,hp.1,?_,?_⟩
  · intro k
    exact PaperP1.Probability.observedCountLaw_coeff G μ J hJ k
  · rw [totalMass_eq_source]
    exact hp.2
  · exact PaperP1.Probability.centered_measure_expansion G μ J hJ

/-- Each positive kernel has the actual prefix/suffix joint expectation as
its coefficients and exactly the prefix activation probability as mass/norm.
The suffix is allowed to depend on the entire prefix. -/
theorem positive_stopped_kernel [MeasurableSpace Ω] [Fintype ι] [LinearOrder ι]
    (G : Finset ι) (D : Finset ι → Prop) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x))
    (hD : Hereditary D) (h0 : D ∅) :
    totalMass (retainedReference G D μ J)=1 ∧
    ∃ K : Finset ι → SignedLaw,
      countLaw G μ J-retainedReference G D μ J=
        ∑ I ∈ boundary G D, difference^I.card*K I ∧
      (∀ I k, (K I).coeff k=∫ ω, (∏ x ∈ I, indicator (J x ω))*
        (if count (suffix G I) J ω=k then 1 else 0) ∂μ) ∧
      ∀ I, (∀ k, 0 ≤ (K I).coeff k) ∧
        totalMass (K I)=μ.real {ω | ∀ x ∈ I, J x ω=true} ∧
        l1Norm (K I)=μ.real {ω | ∀ x ∈ I, J x ω=true} :=
by
  constructor
  · rw [totalMass_eq_source,retainedReference_eq_source]
    exact PaperP1.Probability.measureRetainedReference_mass G D μ J hJ h0
  · refine ⟨PaperP1.Probability.measureBoundaryKernel G μ J hJ,?_,?_,?_⟩
    · rw [countLaw_eq_source G μ J hJ,retainedReference_eq_source]
      exact PaperP1.Probability.stopped_measure_count_difference G D μ J hJ hD h0
    · intro I k
      exact PaperP1.Probability.measureBoundaryKernel_coeff G μ J hJ I k
    · intro I
      refine ⟨PaperP1.Probability.measureBoundaryKernel_nonneg G μ J hJ I,?_,?_⟩
      · rw [totalMass_eq_source,PaperP1.Probability.measureBoundaryKernel_mass,
          PaperP1.Probability.measureJointMoment_eq_probability μ J hJ]
      · rw [l1Norm_eq_source,PaperP1.Probability.measureBoundaryKernel_l1Norm,
          PaperP1.Probability.measureJointMoment_eq_probability μ J hJ]

/-- Ordinary l1 error depends only on the ordered boundary activity mass;
there is no factor charging the number of dependent suffix indicators. -/
theorem stopped_l1_bound [MeasurableSpace Ω] [Fintype ι] [LinearOrder ι]
    (G : Finset ι) (D : Finset ι → Prop) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x))
    (hD : Hereditary D) (h0 : D ∅) :
    l1Norm (countLaw G μ J-retainedReference G D μ J) ≤
      ∑ I ∈ boundary G D, (2 : ℝ)^I.card*μ.real {ω | ∀ x ∈ I, J x ω=true} :=
by
  rw [l1Norm_eq_source,countLaw_eq_source G μ J hJ,retainedReference_eq_source,boundary_eq_source]
  simpa only [PaperP1.Probability.measureJointMoment_eq_probability μ J hJ] using
    PaperP1.Probability.stopped_measure_count_l1_bound G D μ J hJ hD h0

end PaperP1Registry.DependentExpansion
