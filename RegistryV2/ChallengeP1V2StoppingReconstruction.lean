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

/-! # P1 V2: Stopping, heterogeneous conversion and complete-law reconstruction

Selected statements cover main article results 4.1–4.2,5.1–5.3. Literal definitions specify
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
@[expose] public noncomputable section

namespace PaperP1Registry.V2.StoppingReconstruction
open Finset MeasureTheory
open scoped BigOperators
open scoped Classical ENNReal

/-- Prime signs are represented by bits: zero means +1 and one means -1. -/
abbrev F₂ := ZMod 2
local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance measurableF₂ : MeasurableSpace F₂ := ⊤
abbrev Sample := ℕ → F₂

/-- A fair prime-sign bit, with its discrete sigma algebra. -/
def coordinateMeasure : Measure F₂ := Measure.uniformOfFinset (univ : Finset F₂)
instance coordinateProbability : IsProbabilityMeasure coordinateMeasure := by
  constructor
  rw [coordinateMeasure,Measure.uniformOfFinset_apply]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- Independent fair bits, indexed in increasing prime order. -/
def primeSignMeasure : Measure Sample := Measure.infinitePi (fun _ : ℕ ↦ coordinateMeasure)
instance primeSignProbability : IsProbabilityMeasure primeSignMeasure := by
  unfold primeSignMeasure
  infer_instance

/-- Exponent parities of an integer's prime factorization. -/
def parity (n : ℕ) : ℕ →₀ F₂ := n.factorization.mapRange (fun e : ℕ ↦ (e : F₂)) (by simp)

/-- The actual completely multiplicative value, represented as a sign bit.
Prime p uses its coordinate primeCounting' p. -/
def valueBit (ω : Sample) (n : ℕ) : F₂ :=
  (parity n).sum fun p e ↦ ω (Nat.primeCounting' p)*e

/-- A start has the opposite preceding sign and a constant following word.
Both signs are counted; the boundary condition prevents counting interior shifts. -/
def StartEvent (g : ℕ → F₂) (x L : ℕ) : Prop :=
  g (x-1)+g x=1 ∧ ∀ j : ℕ, j<L → g (x+j)=g x
def startIndicator (x L : ℕ) (ω : Sample) : Bool := decide (StartEvent (valueBit ω) x L)

/-- Number of actual run starts in the complete dyadic block [N,2N). -/
def runCount (N L : ℕ) (ω : Sample) : ℕ :=
  ∑ x ∈ Ico N (2*N), (startIndicator x L ω).toNat

/-- Actual moments under the prime-sign law. -/
def moment (N L j : ℕ) : ℝ := ∫ ω, (runCount N L ω : ℝ)^j ∂primeSignMeasure
def actualMean (N L : ℕ) : ℝ := moment N L 1

/-- The second factorial cumulant, with every actual marginal retained. -/
def secondCumulant (N L : ℕ) : ℝ := moment N L 2-actualMean N L-(actualMean N L)^2

/-- Actual singleton probabilities of the complete count law. -/
def sourceMass (N L k : ℕ) : ℝ := primeSignMeasure.real {ω | runCount N L ω=k}
def indicator (x L : ℕ) (ω : Sample) : ℝ := if startIndicator x L ω then 1 else 0

/-- Actual heterogeneous one-window probability. -/
def marginal (x L : ℕ) : ℝ := ∫ ω, indicator x L ω ∂primeSignMeasure

/-- Actual joint start mass, including incompatible families. -/
def jointMoment (L : ℕ) (A : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ A, indicator x L ω ∂primeSignMeasure

/-- Actual centered joint coefficient, using every window's own mean. -/
def centeredCoefficient (L : ℕ) (A : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ A, (indicator x L ω-marginal x L) ∂primeSignMeasure

/-- Actual falling-factorial moment of the complete count. -/
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

/-- Effective square classes: local relations are quotiented out once. -/
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

/-- Connectedness is the actual finest direct partition, not pairwise overlap. -/
def Connected (L : ℕ) (I : Finset ℕ) : Prop := canonicalPartition (fun i : I ↦ space i.val L)=⊤
def connectedFamilies (N L r : ℕ) : Finset (Finset ℕ) :=
  ((Ico N (2*N)).powersetCard r).filter (Connected L)
def relativeNullity (L : ℕ) (I : Finset ℕ) : ℕ :=
  Module.finrank F₂ (LinearMap.ker (addition (fun i : I ↦ space i.val L)))
def compatibleNullity (L : ℕ) (I : Finset ℕ) : ℕ :=
  I.powerset.sup fun A ↦ if 0 < jointMoment L A then relativeNullity L A else 0

/- Zero-target homogeneous mass, equivalently the reciprocal effective rank. -/
open Finset MeasureTheory
open scoped Classical BigOperators

variable {ι Ω : Type*}

/-- Prefix with the greatest element removed, also defined on the empty set. -/
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

/-- Ordinary unweighted singleton l1 norm. -/
def expansion_l1Norm (ν : expansion_SignedLaw) : ℝ := ν.coeff.sum fun _ r ↦ |r|
def expansion_totalMass (ν : expansion_SignedLaw) : ℝ := ν.coeff.sum fun _ r ↦ r
def expansion_indicator (b : Bool) : ℝ := if b then 1 else 0
def expansion_count (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) : ℕ :=
  ∑ x ∈ G, (J x ω).toNat

/-- All expansion_count probabilities, represented on their literal finite support. -/
def expansion_countLaw [MeasurableSpace Ω] (G : Finset ι) (μ : Measure Ω)
    (J : ι → Ω → Bool) : expansion_SignedLaw :=
  ∑ k ∈ range (G.card+1), AddMonoidAlgebra.single k (μ.real {ω | expansion_count G J ω=k})
def expansion_jointMoment [MeasurableSpace Ω] (μ : Measure Ω) (J : ι → Ω → Bool)
    (I : Finset ι) : ℝ := ∫ ω, ∏ x ∈ I, expansion_indicator (J x ω) ∂μ
def expansion_retainedReference [MeasurableSpace Ω] (G : Finset ι) (D : Finset ι → Prop)
    (μ : Measure Ω) (J : ι → Ω → Bool) : expansion_SignedLaw :=
  ∑ I ∈ expansion_retained G D, expansion_scalar (expansion_jointMoment μ J I)*expansion_difference^I.card


/-- Finite reconstruction uses the literal coefficient sequence. -/
theorem expansion_polynomial_expansion {R : Type*} [LinearOrder ι] [CommSemiring R]
    (G : Finset ι) (D : Finset ι → Prop) (u : ι → R) (t : R)
    (hD : expansion_Hereditary D) (h0 : D ∅) :
    (∏ x ∈ G, (1+t*u x))=
      (∑ I ∈ expansion_retained G D, t^I.card*∏ x ∈ I, u x)+
      ∑ I ∈ expansion_boundary G D, (t^I.card*∏ x ∈ I, u x)*
        ∏ y ∈ expansion_suffix G I, (1+t*u y) :=
by sorry
theorem expansion_positive_stopped_kernel [MeasurableSpace Ω] [Fintype ι] [LinearOrder ι]
    (G : Finset ι) (D : Finset ι → Prop) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x))
    (hD : expansion_Hereditary D) (h0 : D ∅) :
    expansion_totalMass (expansion_retainedReference G D μ J)=1 ∧
    ∃ K : Finset ι → expansion_SignedLaw,
      expansion_countLaw G μ J-expansion_retainedReference G D μ J=
        ∑ I ∈ expansion_boundary G D, expansion_difference^I.card*K I ∧
      (∀ I k, (K I).coeff k=∫ ω, (∏ x ∈ I, expansion_indicator (J x ω))*
        (if expansion_count (expansion_suffix G I) J ω=k then 1 else 0) ∂μ) ∧
      ∀ I, (∀ k, 0 ≤ (K I).coeff k) ∧
        expansion_totalMass (K I)=μ.real {ω | ∀ x ∈ I, J x ω=true} ∧
        expansion_l1Norm (K I)=μ.real {ω | ∀ x ∈ I, J x ω=true} :=
by sorry
theorem expansion_stopped_l1_bound [MeasurableSpace Ω] [Fintype ι] [LinearOrder ι]
    (G : Finset ι) (D : Finset ι → Prop) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x))
    (hD : expansion_Hereditary D) (h0 : D ∅) :
    expansion_l1Norm (expansion_countLaw G μ J-expansion_retainedReference G D μ J) ≤
      ∑ I ∈ expansion_boundary G D, (2 : ℝ)^I.card*μ.real {ω | ∀ x ∈ I, J x ω=true} :=
by sorry
def poissonMass (μ : ℝ) (k : ℕ) : ℝ := Real.exp (-μ)*μ^k/(k.factorial : ℝ)
def shift (a : ℕ → ℝ) : ℕ → ℝ | 0 => 0 | k+1 => a k
def quadraticMass (μ α : ℝ) (k : ℕ) : ℝ := poissonMass μ k+
  (α/2)*(shift (shift (poissonMass μ)) k-2*shift (poissonMass μ) k+poissonMass μ k)
def quadraticError (N L : ℕ) : ℝ :=
  ∑' k : ℕ, |sourceMass N L k-quadraticMass (actualMean N L) (secondCumulant N L) k|
def finiteReference {κ : Type*} [DecidableEq κ] (G : Finset κ) (E : Finset (Finset κ))
    (p : κ → ℝ) (c : Finset κ → ℝ) : expansion_SignedLaw :=
  (∏ i ∈ G, expansion_bernoulli (p i))+
    ∑ e ∈ E, expansion_scalar (c e)*expansion_difference^2*
      ∏ i ∈ G \ e, expansion_bernoulli (p i)
def pairReference (N L : ℕ) : expansion_SignedLaw :=
  finiteReference (Ico N (2*N)) ((Ico N (2*N)).powersetCard 2)
    (fun x ↦ marginal x L) (centeredCoefficient L)
def fixedFamilies (N L r : ℕ) : Finset (Finset ℕ) :=
  (connectedFamilies N L r).filter fun I ↦ compatibleNullity L I ≤ 2*L

/-- Exactly254 fixed-order activity assumptions, with constants before the scale. -/
def FixedActivity (C β : ℝ) : Prop :=
  ∀ r : ℕ, 3 ≤ r → r ≤ 256 → ∀ ε : ℝ, 0 < ε →
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      (∑ I ∈ fixedFamilies N L r, |centeredCoefficient L I|) ≤ A*(N : ℝ)^(-β+ε)
theorem prefix_suffix {κ : Type*} [LinearOrder κ] (I G : Finset κ) (hne : I.Nonempty) :
    expansion_properPrefix I=I.erase (I.max' hne) ∧
    expansion_suffix G I=G.filter (fun y ↦ ∀ x ∈ I, x<y) :=
by sorry
theorem finite_conversion {κ : Type*} [DecidableEq κ]
    (G : Finset κ) (E : Finset (Finset κ)) (p : κ → ℝ) (c : Finset κ → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card=2) (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1)
    (P : ℝ) (hP : 0 ≤ P) (hcap : ∀ i ∈ G, p i ≤ P) :
    (∑' k : ℕ, |(finiteReference G E p c).coeff k-
      quadraticMass (∑ i ∈ G, p i) (2*(∑ e ∈ E, c e)-∑ i ∈ G, (p i)^2) k|) ≤
      16*Real.exp 2*((∑ i ∈ G, (p i)^3)+(∑ i ∈ G, (p i)^2)^2+
        (∑ e ∈ E, |c e|)*((∑ i ∈ G, (p i)^2)+P)) :=
by sorry
theorem run_conversion (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      (∑' k : ℕ, |(pairReference N L).coeff k-
        quadraticMass (actualMean N L) (secondCumulant N L) k|) ≤ (N : ℝ)^(-5/3+ε) :=
by sorry
theorem conditional_transfer (C β ε : ℝ) (hβ : 1 < β) (hβcap : β ≤ 4/3) (hε : 0 < ε)
    (hfixed : FixedActivity C β) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → quadraticError N L ≤ (N : ℝ)^(-β+ε) :=
by sorry
theorem triple_reconstruction (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      quadraticError N L ≤ (N : ℝ)^ε*
        (∑ I ∈ (Ico N (2*N)).powersetCard 3, |centeredCoefficient L I|)+(N : ℝ)^(-4/3+ε) ∧
      quadraticError N L ≤ (N : ℝ)^(-4/3+ε) :=
by sorry

end PaperP1Registry.V2.StoppingReconstruction
