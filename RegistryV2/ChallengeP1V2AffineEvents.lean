module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Tactic.Ring.Basic

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! # P1 V2: Exact affine events and homogeneous envelopes

Selected statements cover main article results 2.1–2.5. Literal definitions specify
the independent prime-sign model, exact observables, reference laws and error
norms. Parameters and thresholds retain their printed order. The companion
supplies substantive proofs through the parent development in this repository.
The corresponding six-dossier coverage map records each complete clause bundle.
Only the selected Challenge theorem proofs are deliberate statement holes;
the Solution and its bridge proofs contain no placeholders.
Selected model foundations are adapted through P1 from Paper C, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0; see docs/PAPER_C_REUSE.md.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace PaperP1Registry.V2.AffineEvents

open Finset MeasureTheory

open scoped BigOperators

open scoped Classical ENNReal

open Finset MeasureTheory

open scoped Classical BigOperators

variable {ι Ω : Type*}
abbrev F₂ := ZMod 2

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local instance measurableF₂ : MeasurableSpace F₂ := ⊤
abbrev Sample := ℕ → F₂
def coordinateMeasure : Measure F₂ := Measure.uniformOfFinset (univ : Finset F₂)
instance coordinateProbability : IsProbabilityMeasure coordinateMeasure := by
  constructor
  rw [coordinateMeasure,Measure.uniformOfFinset_apply]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)
def primeSignMeasure : Measure Sample := Measure.infinitePi (fun _ : ℕ ↦ coordinateMeasure)
instance primeSignProbability : IsProbabilityMeasure primeSignMeasure := by
  unfold primeSignMeasure
  infer_instance
def parity (n : ℕ) : ℕ →₀ F₂ := n.factorization.mapRange (fun e : ℕ ↦ (e : F₂)) (by simp)
def valueBit (ω : Sample) (n : ℕ) : F₂ :=
  (parity n).sum fun p e ↦ ω (Nat.primeCounting' p)*e
def StartEvent (g : ℕ → F₂) (x L : ℕ) : Prop :=
  g (x-1)+g x=1 ∧ ∀ j : ℕ, j<L → g (x+j)=g x
def startIndicator (x L : ℕ) (ω : Sample) : Bool := decide (StartEvent (valueBit ω) x L)
def runCount (N L : ℕ) (ω : Sample) : ℕ :=
  ∑ x ∈ Ico N (2*N), (startIndicator x L ω).toNat
def moment (N L j : ℕ) : ℝ := ∫ ω, (runCount N L ω : ℝ)^j ∂primeSignMeasure
def actualMean (N L : ℕ) : ℝ := moment N L 1
def secondCumulant (N L : ℕ) : ℝ := moment N L 2-actualMean N L-(actualMean N L)^2
def sourceMass (N L k : ℕ) : ℝ := primeSignMeasure.real {ω | runCount N L ω=k}
def nominalMean (N L : ℕ) : ℝ := (N : ℝ)*(2^L : ℝ)⁻¹
def indicator (x L : ℕ) (ω : Sample) : ℝ := if startIndicator x L ω then 1 else 0
def marginal (x L : ℕ) : ℝ := ∫ ω, indicator x L ω ∂primeSignMeasure
def jointMoment (L : ℕ) (A : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ A, indicator x L ω ∂primeSignMeasure
def centeredCoefficient (L : ℕ) (A : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ A, (indicator x L ω-marginal x L) ∂primeSignMeasure
def factorialMoment (N L r : ℕ) : ℝ :=
  ∫ ω, ((runCount N L ω).descFactorial r : ℝ) ∂primeSignMeasure
def thirdCumulant (N L : ℕ) : ℝ :=
  factorialMoment N L 3-3*factorialMoment N L 2*factorialMoment N L 1+2*(factorialMoment N L 1)^3
def fourthCumulant (N L : ℕ) : ℝ :=
  factorialMoment N L 4-4*factorialMoment N L 3*factorialMoment N L 1-
    3*(factorialMoment N L 2)^2+12*factorialMoment N L 2*(factorialMoment N L 1)^2-
    6*(factorialMoment N L 1)^4
def principalSecondScale (N L : ℕ) : ℝ :=
  (((L%3 : ℕ) : ℝ)+2)/(18*(2 : ℝ)^(((L%3 : ℕ) : ℝ)/3))*
    (nominalMean N L)^(5/3 : ℝ)*L*(N : ℝ)^(-2/3 : ℝ)
def vertexLabel (x L : ℕ) (v : Fin (L+1)) : ℕ :=
  if v.val=0 then x-1 else x+(v.val-1)
def vertexSum (L : ℕ) : (Fin (L+1) → F₂) →ₗ[F₂] F₂ where
  toFun w := ∑ v : Fin (L+1), w v
  map_add' w z := by simp only [Pi.add_apply,Finset.sum_add_distrib]
  map_smul' c w := by
    change (∑ v : Fin (L+1), c*w v)=c*∑ v : Fin (L+1), w v
    rw [Finset.mul_sum]
def vertexParity (x L : ℕ) : (Fin (L+1) → F₂) →ₗ[F₂] (ℕ →₀ F₂) :=
  Fintype.linearCombination F₂ (fun v ↦ parity (vertexLabel x L v))
def evenParity (x L : ℕ) : LinearMap.ker (vertexSum L) →ₗ[F₂] (ℕ →₀ F₂) :=
  (vertexParity x L).comp (LinearMap.ker (vertexSum L)).subtype
def space (x L : ℕ) : Submodule F₂ (ℕ →₀ F₂) := LinearMap.range (evenParity x L)
def addition {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) : ((i : ι) → S i) →ₗ[F₂] U where
  toFun s := ∑ i, (s i).val
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum]
def RespectsRelations {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule F₂ U) (P : Finpartition (univ : Finset ι)) : Prop :=
  ∀ s : (i : ι) → S i, addition S s=0 → ∀ C ∈ P.parts, ∑ i ∈ C, (s i).val=0
def canonicalPartition {U ι : Type*} [AddCommGroup U] [Module F₂ U]
    [Fintype ι] [DecidableEq ι] (S : ι → Submodule F₂ U) : Finpartition (univ : Finset ι) :=
  ((univ : Finset (Finpartition (univ : Finset ι))).filter (RespectsRelations S)).inf id
def Connected (L : ℕ) (I : Finset ℕ) : Prop := canonicalPartition (fun i : I ↦ space i.val L)=⊤
def connectedFamilies (N L r : ℕ) : Finset (Finset ℕ) :=
  ((Ico N (2*N)).powersetCard r).filter (Connected L)
def relativeNullity (L : ℕ) (I : Finset ℕ) : ℕ :=
  Module.finrank F₂ (LinearMap.ker (addition (fun i : I ↦ space i.val L)))
def compatibleNullity (L : ℕ) (I : Finset ℕ) : ℕ :=
  I.powerset.sup fun A ↦ if 0 < jointMoment L A then relativeNullity L A else 0
def totalSpace (L : ℕ) (I : Finset ℕ) : Submodule F₂ (ℕ →₀ F₂) :=
  ⨆ i : I, space i.val L
def homogeneousMass (L : ℕ) (I : Finset ℕ) : ℝ :=
  (2 ^ Module.finrank F₂ (totalSpace L I) : ℝ)⁻¹
def rankWeight (L : ℕ) (I : Finset ℕ) : ℝ :=
  (∏ x ∈ I, marginal x L)*(2 ^ relativeNullity L I : ℝ)
def expansion_properPrefix [LinearOrder ι] (I : Finset ι) : Finset ι :=
  I.filter fun x ↦ ∃ y ∈ I, x<y
def expansion_Hereditary (D : Finset ι → Prop) : Prop :=
  ∀ ⦃I J⦄, J ⊆ I → D I → D J
def expansion_Boundary [LinearOrder ι] (D : Finset ι → Prop) (I : Finset ι) : Prop :=
  ¬ D I ∧ D (expansion_properPrefix I)
def expansion_suffix [LinearOrder ι] (G I : Finset ι) : Finset ι :=
  G.filter fun y ↦ ∀ x ∈ I, x<y
def expansion_retained (G : Finset ι) (D : Finset ι → Prop) : Finset (Finset ι) :=
  G.powerset.filter D
def expansion_boundary [LinearOrder ι] (G : Finset ι) (D : Finset ι → Prop) : Finset (Finset ι) :=
  G.powerset.filter (expansion_Boundary D)
abbrev expansion_SignedLaw := AddMonoidAlgebra ℝ ℕ
def expansion_scalar (r : ℝ) : expansion_SignedLaw := AddMonoidAlgebra.single 0 r
def expansion_atom (k : ℕ) : expansion_SignedLaw := AddMonoidAlgebra.single k 1
def expansion_difference : expansion_SignedLaw := expansion_atom 1-expansion_atom 0
def expansion_bernoulli (p : ℝ) : expansion_SignedLaw := expansion_atom 0+expansion_scalar p*expansion_difference
def expansion_l1Norm (ν : expansion_SignedLaw) : ℝ := ν.coeff.sum fun _ r ↦ |r|
def expansion_totalMass (ν : expansion_SignedLaw) : ℝ := ν.coeff.sum fun _ r ↦ r
def expansion_indicator (b : Bool) : ℝ := if b then 1 else 0
def expansion_count (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) : ℕ :=
  ∑ x ∈ G, (J x ω).toNat
def expansion_countLaw [MeasurableSpace Ω] (G : Finset ι) (μ : Measure Ω)
    (J : ι → Ω → Bool) : expansion_SignedLaw :=
  ∑ k ∈ range (G.card+1), AddMonoidAlgebra.single k (μ.real {ω | expansion_count G J ω=k})
def expansion_jointMoment [MeasurableSpace Ω] (μ : Measure Ω) (J : ι → Ω → Bool)
    (I : Finset ι) : ℝ := ∫ ω, ∏ x ∈ I, expansion_indicator (J x ω) ∂μ
def expansion_marginal [MeasurableSpace Ω] (μ : Measure Ω) (J : ι → Ω → Bool) (x : ι) : ℝ :=
  ∫ ω, expansion_indicator (J x ω) ∂μ
def expansion_centeredMoment [MeasurableSpace Ω] (μ : Measure Ω) (J : ι → Ω → Bool)
    (I : Finset ι) : ℝ :=
  ∫ ω, ∏ x ∈ I, (expansion_indicator (J x ω)-expansion_marginal μ J x) ∂μ
def expansion_retainedReference [MeasurableSpace Ω] (G : Finset ι) (D : Finset ι → Prop)
    (μ : Measure Ω) (J : ι → Ω → Bool) : expansion_SignedLaw :=
  ∑ I ∈ expansion_retained G D, expansion_scalar (expansion_jointMoment μ J I)*expansion_difference^I.card
instance finiteSpace (x L : ℕ) : Fintype (space x L) := by
  classical
  let : Fintype (LinearMap.ker (vertexSum L)) := Fintype.ofFinite _
  exact Fintype.ofSurjective (evenParity x L).rangeRestrict (by
    rintro ⟨c,⟨w,hw⟩⟩
    exact ⟨w,Subtype.ext hw⟩)
def PrimeUpTo (M : ℕ) := {p : Fin (M+1) // Nat.Prime p.val}
instance (M : ℕ) : Fintype (PrimeUpTo M) := Subtype.fintype _
abbrev FiniteSample (M : ℕ) := PrimeUpTo M → F₂
def finiteValue (M n : ℕ) : FiniteSample M →ₗ[F₂] F₂ where
  toFun ω := ∑ p : PrimeUpTo M, ω p*parity n p.val
  map_add' := by intros; simp [add_mul,Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum,mul_assoc]
def startRow (M x L : ℕ) (i : Fin L) : FiniteSample M →ₗ[F₂] F₂ :=
  if i.val=0 then finiteValue M (x-1)+finiteValue M x
  else finiteValue M x+finiteValue M (x+i.val)
def startSystem (M x L : ℕ) : FiniteSample M →ₗ[F₂] (Fin L → F₂) := LinearMap.pi (startRow M x L)
def startRhs (L : ℕ) : Fin L → F₂ := fun i ↦ if i.val=0 then 1 else 0
def familyCentered {ι : Type*} [Fintype ι] (L : ℕ) (g : ι → ℕ) : ℝ :=
  ∫ ω, ∏ i, (indicator (g i) L ω-marginal (g i) L) ∂primeSignMeasure
def familyNullity {ι : Type*} [Fintype ι] (L : ℕ) (g : ι → ℕ) : ℕ :=
  Module.finrank F₂ (LinearMap.ker (addition (fun i ↦ space (g i) L)))
def FullRelation {ι : Type*} [Fintype ι] (L : ℕ) (g : ι → ℕ)
    (s : (i : ι) → space (g i) L) : Prop := (∀ i, s i≠0) ∧ addition (fun i ↦ space (g i) L) s=0
def tupleSign {ι : Type*} [Fintype ι] (M L : ℕ) (g : ι → ℕ)
    (a : ι → FiniteSample M) (s : (i : ι) → space (g i) L) : ℝ :=
  ∏ i, if (∑ p : PrimeUpTo M, a i p*(s i).val p.val)=0 then 1 else -1
def partImage {I : Finset ℕ} (C : Finset I) : Finset ℕ := C.image fun i ↦ i.val
theorem expansion_centered_identity [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    (∀ k, (expansion_countLaw G μ J).coeff k=μ.real {ω | expansion_count G J ω=k}) ∧
    (∀ k, 0 ≤ (expansion_countLaw G μ J).coeff k) ∧ expansion_totalMass (expansion_countLaw G μ J)=1 ∧
    expansion_countLaw G μ J=∑ I ∈ G.powerset, expansion_scalar (expansion_centeredMoment μ J I)*
      expansion_difference^I.card*∏ x ∈ G \ I, expansion_bernoulli (expansion_marginal μ J x) :=
by sorry
theorem original_fourier {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M L : ℕ) (g : ι → ℕ) (hL : 0 < L) (hcut : ∀ i, g i+L ≤ M)
    (hp : ∀ i, 0 < marginal (g i) L) :
    ∃ a : ι → FiniteSample M, (∀ i, startSystem M (g i) L (a i)=startRhs L) ∧
      familyCentered L g=(∏ i, marginal (g i) L)*
        (∑ s : (i : ι) → space (g i) L, if FullRelation L g s then tupleSign M L g a s else 0) ∧
      |familyCentered L g| ≤ (∏ i, marginal (g i) L)*((2 ^ familyNullity L g : ℝ)-1) ∧
      |familyCentered L g| ≤ (∏ i, marginal (g i) L)*(2 ^ familyNullity L g : ℝ) ∧
      (familyCentered L g≠0 → ∃ s : (i : ι) → space (g i) L, FullRelation L g s) :=
by sorry
theorem finite_envelope (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hne : I.Nonempty) :
    homogeneousMass L I=(∏ x ∈ I, (2 ^ Module.finrank F₂ (space x L) : ℝ)⁻¹)*
      (2 ^ relativeNullity L I : ℝ) ∧
    rankWeight L I ≤ homogeneousMass L I ∧ jointMoment L I ≤ homogeneousMass L I ∧
      |centeredCoefficient L I| ≤ homogeneousMass L I :=
by sorry
theorem nominal_envelope (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∀ I : Finset ℕ, I ⊆ Ico N (2*N) →
        homogeneousMass L I ≤ (2 : ℝ)^I.card*((2 ^ L : ℝ)⁻¹)^I.card*
          (2 ^ relativeNullity L I : ℝ) :=
by sorry
theorem compatible_nullity (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hp : ∀ x ∈ I, 0 < marginal x L) :
    |centeredCoefficient L I| ≤ (2 : ℝ)^I.card*(∏ x ∈ I, marginal x L)*
      (2 ^ compatibleNullity L I : ℝ) ∧
    compatibleNullity L I ≤ relativeNullity L I ∧
    (0 < jointMoment L I → compatibleNullity L I=relativeNullity L I) :=
by sorry
theorem unique_direct_partition {U ι : Type*} [AddCommGroup U] [Module F₂ U]
    [Fintype ι] [DecidableEq ι] (S : ι → Submodule F₂ U) :
    ∃! P : Finpartition (univ : Finset ι), RespectsRelations S P ∧
      ∀ Q : Finpartition (univ : Finset ι), RespectsRelations S Q → P ≤ Q :=
by sorry
theorem canonical_factorization (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    let P := canonicalPartition (fun i : I ↦ space i.val L)
    RespectsRelations (fun i : I ↦ space i.val L) P ∧
    (∀ Q : Finpartition (univ : Finset I), RespectsRelations (fun i : I ↦ space i.val L) Q → P ≤ Q) ∧
    jointMoment L I=∏ C ∈ P.parts, jointMoment L (partImage C) ∧
    centeredCoefficient L I=∏ C ∈ P.parts, centeredCoefficient L (partImage C) ∧
    relativeNullity L I=∑ C ∈ P.parts, relativeNullity L (partImage C) :=
by sorry
theorem expansion_probability_clauses {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace Ω] (G : Finset κ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : κ → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    expansion_centeredMoment μ J ∅=1 ∧
    (∀ x, expansion_centeredMoment μ J {x}=0) ∧
    ∀ I : Finset κ,
      (∀ k, 0≤(∏ x ∈ G \ I, expansion_bernoulli (expansion_marginal μ J x)).coeff k) ∧
      expansion_totalMass (∏ x ∈ G \ I, expansion_bernoulli (expansion_marginal μ J x))=1 :=
by sorry

end PaperP1Registry.V2.AffineEvents
