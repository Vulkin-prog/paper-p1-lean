module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import PaperP1.Probability.PositionalBlockIndependence

/-! # Exact probability structure of the compensated Poisson reference field

The finite ground, packet incidence, nonnegative compensated rates, genuine
product Poisson law and natural-valued coordinates are explicit Mathlib-only
definitions. The statements concern the reference field in main lemma 20.1,
with arbitrary finite packets and heterogeneous intensities where indicated.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1Registry.PoissonReference

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

local instance referenceDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def incidence (E : Finset (Finset ℕ)) (q : Finset ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ e∈E,if x∈e then q e else 0

abbrev Channel (G : Finset ℕ) (E : Finset (Finset ℕ)) := ↥G ⊕ ↥E

def arrivalRate (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e) : Channel G E → ℝ≥0
  | Sum.inl x => ⟨p x.val-incidence E q x.val,hp x.val x.property⟩
  | Sum.inr e => ⟨q e.val,hq e.val e.property⟩

def arrivalMeasure (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e) :
    Measure (Channel G E → ℕ) :=
  Measure.pi (fun a ↦ poissonMeasure (arrivalRate G E p q hp hq a))

def field (G : Finset ℕ) (E : Finset (Finset ℕ))
    (ω : Channel G E → ℕ) (x : G) : ℕ :=
  ω (Sum.inl x)+∑ e : E,if x.val∈e.val then ω (Sum.inr e) else 0

def block (G : Finset ℕ) (E : Finset (Finset ℕ)) (A : Finset G) :
    (Channel G E → ℕ) → (A → ℕ) := fun ω x ↦ field G E ω x.val


theorem incidence_eq (E : Finset (Finset ℕ)) (q : Finset ℕ → ℝ) (x : ℕ) :
    incidence E q x=PaperP1.PositionalCompoundPoisson.incidence E q x := by
  unfold incidence PaperP1.PositionalCompoundPoisson.incidence
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hx : x∈e
  · simp only [hx,ite_true]
  · simp only [hx,ite_false]

theorem source_single_nonneg (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) :
    ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x := by
  simpa only [incidence_eq] using hp

theorem arrivalRate_eq (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x)
    (hpS : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) :
    arrivalRate G E p q hp hq=
      PaperP1.PositionalPoissonRealization.channelRate G E p q hpS hq := by
  funext a
  apply Subtype.ext
  cases a with
  | inl x =>
    change p x.val-incidence E q x.val=
      p x.val-PaperP1.PositionalCompoundPoisson.incidence E q x.val
    rw [incidence_eq]
  | inr e => rfl

theorem arrivalMeasure_eq (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x)
    (hpS : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) :
    arrivalMeasure G E p q hp hq=
      (PaperP1.PositionalPoissonRealization.poissonProduct
        (PaperP1.PositionalPoissonRealization.channelRate G E p q hpS hq)).val := by
  unfold arrivalMeasure
  rw [arrivalRate_eq G E p q hp hpS hq]
  rfl

theorem field_eq (G : Finset ℕ) (E : Finset (Finset ℕ))
    (ω : Channel G E → ℕ) (x : G) :
    field G E ω x=(∑ a : Channel G E,
      ω a • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val := by
  rw [PaperP1.PositionalPoissonRealization.field_coordinate]
  unfold field
  congr 1
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hx : x.val∈e.val
  · simp only [hx,ite_true]
  · simp only [hx,ite_false]

theorem field_function_eq (G : Finset ℕ) (E : Finset (Finset ℕ)) (x : G) :
    (fun ω ↦ field G E ω x)=(fun ω ↦ (∑ a : Channel G E,
      ω a • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val) := by
  funext ω
  exact field_eq G E ω x

theorem realField_eq (G : Finset ℕ) (E : Finset (Finset ℕ)) (x : G) :
    (fun ω ↦ (field G E ω x : ℝ))=
      PaperP1.PositionalArrivalCovariance.coordinate G E (fun a ω ↦ ω a) x := by
  funext ω
  exact congrArg (fun n : ℕ ↦ (n : ℝ)) (field_eq G E ω x)

theorem block_eq (G : Finset ℕ) (E : Finset (Finset ℕ)) (A : Finset G) :
    block G E A=PaperP1.PositionalBlockIndependence.block G E (fun a ω ↦ ω a) A := by
  funext ω x
  exact field_eq G E ω x.val

theorem exact_marginals (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e) (x : G) :
    ∃ r : ℝ≥0,(r : ℝ)=p x.val ∧
      HasLaw (fun ω ↦ field G E ω x) (poissonMeasure r) (arrivalMeasure G E p q hp hq) ∧
      ∀ j : ℕ,Integrable (fun ω ↦ ((field G E ω x).descFactorial j : ℝ))
        (arrivalMeasure G E p q hp hq) ∧
        (∫ ω,((field G E ω x).descFactorial j : ℝ) ∂arrivalMeasure G E p q hp hq)=p x.val^j := by

  let hpS := source_single_nonneg G E p q hp
  obtain ⟨r,hr,hLaw⟩ := PaperP1.PositionalArrivalMarginals.hasLaw_canonical_coordinate
    G E p q hpS hq x
  have hNative : HasLaw (fun ω ↦ field G E ω x) (poissonMeasure r)
      (arrivalMeasure G E p q hp hq) := by
    rw [arrivalMeasure_eq G E p q hp hpS hq,field_function_eq G E x]
    exact hLaw
  refine ⟨r,hr,hNative,?_⟩
  intro j
  have h := PaperP1.PositionalArrivalMarginals.factorial_moment_of_hasLaw
    (arrivalMeasure G E p q hp hq) (fun ω ↦ field G E ω x) r hNative j
  simpa only [hr] using h

theorem covariance_matrix (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e)
    (hE : ∀ e∈E,e.card=2) (x y : G) :
    cov[fun ω ↦ (field G E ω x : ℝ),fun ω ↦ (field G E ω y : ℝ);
      arrivalMeasure G E p q hp hq] =
      if x=y then p x.val else if {x.val,y.val}∈E then q {x.val,y.val} else 0 := by

  let hpS := source_single_nonneg G E p q hp
  have h := PaperP1.PositionalArrivalCovariance.covariance_canonical_pairs
    G E p q hpS hq hE x y
  rw [← arrivalMeasure_eq G E p q hp hpS hq,← realField_eq G E x,← realField_eq G E y] at h
  have hd : (fun a b : ℕ ↦ PaperP1.PositionalArrivalCovariance.covarianceDecidable (a=b))=instDecidableEqNat :=
    Subsingleton.elim _ _
  rw [hd] at h
  exact h

theorem pair_independence (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e)
    (hE : ∀ e∈E,e.card=2) (x y : G) (hxy : x≠y) :
    IndepFun (fun ω ↦ field G E ω x) (fun ω ↦ field G E ω y)
      (arrivalMeasure G E p q hp hq) ↔ {x.val,y.val}∉E ∨ q {x.val,y.val}=0 := by

  let hpS := source_single_nonneg G E p q hp
  let μS := PaperP1.PositionalPoissonRealization.channelRate G E p q hpS hq
  let P : Measure (Channel G E → ℕ) :=
    (PaperP1.PositionalPoissonRealization.poissonProduct μS).val
  let : IsProbabilityMeasure P :=
    (PaperP1.PositionalPoissonRealization.poissonProduct μS).property
  have h := PaperP1.PositionalArrivalIndependence.independent_pair_counts_iff
    G E p q hpS hq hE P (fun a ω ↦ ω a)
    (PaperP1.PositionalPoissonRealization.poissonProduct_hasLaw_eval μS)
    (PaperP1.PositionalPoissonRealization.poissonProduct_independent μS) x y hxy
  dsimp only [P,μS] at h
  rw [← arrivalMeasure_eq G E p q hp hpS hq,
    ← field_function_eq G E x,← field_function_eq G E y] at h
  have hd : (fun a b : ℕ ↦ PaperP1.PositionalArrivalIndependence.independenceDecidable (a=b))=instDecidableEqNat :=
    Subsingleton.elim _ _
  rw [hd] at h
  exact h

theorem block_dependency (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e)
    (hE : ∀ e∈E,e.card=2) (A B : Finset G) (hAB : Disjoint A B) :
    IndepFun (block G E A) (block G E B) (arrivalMeasure G E p q hp hq) ↔
      ∀ x∈A,∀ y∈B,¬({x.val,y.val}∈E ∧ 0<q {x.val,y.val}) := by

  let hpS := source_single_nonneg G E p q hp
  let μS := PaperP1.PositionalPoissonRealization.channelRate G E p q hpS hq
  let P : Measure (Channel G E → ℕ) :=
    (PaperP1.PositionalPoissonRealization.poissonProduct μS).val
  let : IsProbabilityMeasure P :=
    (PaperP1.PositionalPoissonRealization.poissonProduct μS).property
  have h := PaperP1.PositionalBlockIndependence.independent_pair_blocks_iff_no_positive_crossing
    G E p q hpS hq hE P (fun a ω ↦ ω a)
    (PaperP1.PositionalPoissonRealization.poissonProduct_hasLaw_eval μS)
    (PaperP1.PositionalPoissonRealization.poissonProduct_independent μS) A B hAB
  dsimp only [P,μS] at h
  rw [← arrivalMeasure_eq G E p q hp hpS hq,← block_eq G E A,← block_eq G E B] at h
  have hd : (fun a b : ℕ ↦ PaperP1.PositionalBlockIndependence.blockDecidable (a=b))=instDecidableEqNat :=
    Subsingleton.elim _ _
  rw [hd] at h
  exact h


end PaperP1Registry.PoissonReference
