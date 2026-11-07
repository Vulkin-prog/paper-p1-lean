module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import PaperP1.Affine.PartitionMoments
public import PaperP1.Affine.PartitionNullity

/-! # Exact finite affine spectra and their canonical factorization
Uniform averages, actual effective-block indicators, individual rates,
full-support relations and the finest relation-respecting partition are
literal Mathlib constructions. Incompatible prescriptions retain their zero
mass. The foundational affine counting and character calculations are adapted
through P1 from Paper C, commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Apache-2.0; exact source attribution is in docs/PAPER_C_REUSE.md.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1Registry.AffineSpectra
open Finset
open scoped Classical BigOperators

abbrev F₂ := ZMod 2
local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The literal normalized uniform average over a finite carrier. -/
def average {V : Type*} [Fintype V] (f : V → ℝ) : ℝ :=
  ∑ v, (Fintype.card V : ℝ)⁻¹*f v

def solutionMass {V W : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V]
    [AddCommGroup W] [Module F₂ W] (A : V →ₗ[F₂] W) (b : W) : ℝ :=
  average fun v ↦ if A v=b then 1 else 0

def character {V : Type*} [AddCommGroup V] [Module F₂ V]
    (f : V →ₗ[F₂] F₂) (v : V) : ℝ := if f v=0 then 1 else -1

/-- One effective block's actual affine event, with a local compatible target. -/
def indicator {V : Type*} [AddCommGroup V] [Module F₂ V]
    (S : Submodule F₂ (V →ₗ[F₂] F₂)) (a v : V) : ℝ :=
  if ∀ s : S, s.val v=s.val a then 1 else 0

def rate {V : Type*} [AddCommGroup V] [Module F₂ V]
    (S : Submodule F₂ (V →ₗ[F₂] F₂)) [Fintype S] : ℝ :=
  (Fintype.card S : ℝ)⁻¹

/-- Addition from the product of the actual effective spaces. -/
def addition {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) : ((i : ι) → S i) →ₗ[F₂] U where
  toFun := fun s ↦ ∑ i, (s i).val
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum]

def relativeNullity {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) : ℕ := Module.finrank F₂ (LinearMap.ker (addition S))

def FullRelation {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) (s : (i : ι) → S i) : Prop :=
  (∀ i, s i ≠ 0) ∧ addition S s=0

/-- Every relation remains a relation after restriction to any part. -/
def RespectsRelations {U ι : Type*} [AddCommGroup U] [Module F₂ U]
    [Fintype ι] [DecidableEq ι] (S : ι → Submodule F₂ U)
    (P : Finpartition (univ : Finset ι)) : Prop :=
  ∀ s : (i : ι) → S i, addition S s=0 →
    ∀ C ∈ P.parts, ∑ i ∈ C, (s i).val=0

def tupleSign {V ι : Type*} [AddCommGroup V] [Module F₂ V] [Fintype ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) (a : ι → V) (s : (i : ι) → S i) : ℝ :=
  ∏ i, character (s i).val (a i)

def jointMoment {V ι : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V] [Fintype ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) (a : ι → V) : ℝ :=
  average fun v ↦ ∏ i, indicator (S i) (a i) v

def centeredMoment {V ι : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V] [Fintype ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) [∀ i, Fintype (S i)] (a : ι → V) : ℝ :=
  average fun v ↦ ∏ i, (indicator (S i) (a i) v-rate (S i))


theorem average_eq_source {V : Type*} [Fintype V] [Nonempty V] (f : V → ℝ) :
    average f=PaperP1.Algebra.finiteExpectation
      (PaperP1.Probability.uniformFiniteProbability V).weight f := rfl

theorem solutionMass_eq_source {V W : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [AddCommGroup W] [Module F₂ W] (A : V →ₗ[F₂] W) (b : W) :
    solutionMass A b=PaperP1.Affine.uniformSolutionMass A b := rfl

theorem character_eq_source {V : Type*} [AddCommGroup V] [Module F₂ V]
    (f : V →ₗ[F₂] F₂) (v : V) : character f v=PaperP1.Affine.realCharacter f v := by
  by_cases h : f v=0 <;> simp [character,PaperP1.Affine.realCharacter,PaperP1.Affine.binarySign,h]

theorem indicator_eq_source {V : Type*} [AddCommGroup V] [Module F₂ V]
    (S : Submodule F₂ (V →ₗ[F₂] F₂)) (a v : V) :
    indicator S a v=PaperP1.Affine.effectiveIndicator S a v := rfl

theorem rate_eq_source {V : Type*} [AddCommGroup V] [Module F₂ V]
    (S : Submodule F₂ (V →ₗ[F₂] F₂)) [Fintype S] :
    rate S=PaperP1.Affine.effectiveRate S := rfl

theorem addition_eq_source {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) : addition S=PaperP1.Affine.relationAddition S := rfl

theorem relativeNullity_eq_source {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) : relativeNullity S=PaperP1.Affine.relativeNullity S := rfl

theorem fullRelation_iff_source {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) (s : (i : ι) → S i) :
    FullRelation S s ↔ PaperP1.Affine.IsFullSupportRelation S s := Iff.rfl

theorem respectsRelations_iff_source {U ι : Type*} [AddCommGroup U] [Module F₂ U]
    [Fintype ι] [DecidableEq ι] (S : ι → Submodule F₂ U)
    (P : Finpartition (univ : Finset ι)) :
    RespectsRelations S P ↔ PaperP1.Affine.RelationDirectPartition S P := Iff.rfl

theorem tupleSign_eq_source {V ι : Type*} [AddCommGroup V] [Module F₂ V] [Fintype ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) (a : ι → V) (s : (i : ι) → S i) :
    tupleSign S a s=PaperP1.Affine.affineTupleSign S a s := by
  simp only [tupleSign,PaperP1.Affine.affineTupleSign,character_eq_source]

theorem jointMoment_eq_source {V ι : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) (a : ι → V) :
    jointMoment S a=PaperP1.Affine.effectiveJointMoment S a := rfl

theorem centeredMoment_eq_source {V ι : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) [∀ i, Fintype (S i)] (a : ι → V) :
    centeredMoment S a=PaperP1.Affine.effectiveCenteredMoment S a := rfl

/-- Exact mass and positivity of every finite affine system, including all
incompatible systems, using the effective image rank. -/
theorem uniform_affine_mass {V W : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [AddCommGroup W] [Module F₂ W] (A : V →ₗ[F₂] W) (b : W) :
    solutionMass A b=(if b ∈ LinearMap.range A then
      ((2 : ℝ)^(Module.finrank F₂ (LinearMap.range A)))⁻¹ else 0) ∧
    (0<solutionMass A b ↔ b ∈ LinearMap.range A) :=
by
  rw [solutionMass_eq_source]
  constructor
  · by_cases h : b ∈ LinearMap.range A
    · rw [ite_eq_left h]
      exact PaperP1.Affine.uniformSolutionMass_of_compatible A b h
    · rw [ite_eq_right h]
      exact PaperP1.Affine.uniformSolutionMass_of_not_compatible A b h
  · exact PaperP1.Affine.uniformSolutionMass_pos_iff A b

/-- Actual individual marginal rates and the exact centered full-support
Fourier sum, retaining every affine sign and heterogeneous block dimension. -/
theorem centered_fourier_formula {V ι : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) [∀ i, Fintype (S i)] (a : ι → V) :
    (∀ i, average (fun v ↦ indicator (S i) (a i) v)=rate (S i) ∧
      rate (S i)=((2 : ℝ)^(Module.finrank F₂ (S i)))⁻¹ ∧ 0<rate (S i)) ∧
    centeredMoment S a=(∏ i, rate (S i))*
      ∑ s : (i : ι) → S i, if FullRelation S s then tupleSign S a s else 0 :=
by
  constructor
  · intro i
    refine ⟨?_,?_,?_⟩
    · exact PaperP1.Affine.effective_marginal (S i) (a i)
    · have hcard : Fintype.card (S i)=2^(Module.finrank F₂ (S i)) :=
        PaperP1.Affine.card_eq_two_pow_finrank (V := S i)
      simp only [rate,hcard,Nat.cast_pow,Nat.cast_ofNat]
    · exact inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos (α := S i)))
  · simpa only [centeredMoment_eq_source,PaperP1.Affine.effectiveCenteredMoment,rate_eq_source,fullRelation_iff_source,
      tupleSign_eq_source] using PaperP1.Affine.effective_full_support_formula S a

/-- Exact dimension deficit, the sharper 2^rho-1 centered bound, and a
full-support relation whenever the centered moment is nonzero. -/
theorem sharp_relative_nullity_bound {V ι : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) [∀ i, Fintype (S i)] (a : ι → V) :
    relativeNullity S=(∑ i, Module.finrank F₂ (S i))-
      Module.finrank F₂ (⨆ i, S i : Submodule F₂ (V →ₗ[F₂] F₂)) ∧
    |centeredMoment S a| ≤ (∏ i, rate (S i))*((2 : ℝ)^(relativeNullity S)-1) ∧
    (centeredMoment S a ≠ 0 → ∃ s : (i : ι) → S i, FullRelation S s) :=
by
  refine ⟨PaperP1.Affine.relativeNullity_eq_dimension_deficit S,
    PaperP1.Affine.effectiveCenteredMoment_bound S a,?_⟩
  exact PaperP1.Affine.fullSupportRelation_of_centeredMoment_ne_zero S a

/-- The unique finest relation-respecting partition factors both actual
ordinary and centered moments and adds their effective relative nullities. -/
theorem canonical_factorization {V ι : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) [∀ i, Fintype (S i)] :
    ∃! P : Finpartition (univ : Finset ι),
      RespectsRelations S P ∧
      (∀ Q, RespectsRelations S Q → P ≤ Q) ∧
      (∀ a : ι → V,
        jointMoment S a=∏ C : P.parts,
          jointMoment (fun i : C.val ↦ S i.val) (fun i ↦ a i.val) ∧
        centeredMoment S a=∏ C : P.parts,
          centeredMoment (fun i : C.val ↦ S i.val) (fun i ↦ a i.val)) ∧
      relativeNullity S=∑ C : P.parts, relativeNullity (fun i : C.val ↦ S i.val) :=
by
  obtain ⟨P,⟨hP,hfinest⟩,hunique⟩ := PaperP1.Affine.existsUnique_finest_relationPartition S
  refine ⟨P,⟨hP,hfinest,?_,?_⟩,?_⟩
  · intro a
    exact ⟨PaperP1.Affine.effectiveJointMoment_partition S P hP a,
      PaperP1.Affine.effectiveCenteredMoment_partition S P hP a⟩
  · exact PaperP1.Affine.relativeNullity_partition_additive S P hP
  · intro Q hQ
    exact hunique Q ⟨hQ.1,hQ.2.1⟩

end PaperP1Registry.AffineSpectra
