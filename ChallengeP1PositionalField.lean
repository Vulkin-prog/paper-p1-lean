module

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

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic

/-! # The original weighted positional field and its independent Poisson arrivals

The arithmetic good edges, individual joint probabilities, nominal single rates,
original grid and every fixed polynomial weight are literal Mathlib-only data.
Prime-sign and start foundations are adapted through P1 from Paper C commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0; see docs/PAPER_C_REUSE.md.
Only the three selected Challenge statement holes are deliberate placeholders.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1Registry.PositionalField
open Finset MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal

local instance positionalDecidable (P : Prop) : Decidable P := Classical.propDecidable P

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


/-- The complete original dyadic grid. -/
def ground (N : ℕ) : Finset ℕ := Ico N (2*N)

/-- The actual joint start probability, as the integral of its indicator. -/
def jointRate (L : ℕ) (I : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ I, (if startIndicator x L ω then (1 : ℝ) else 0) ∂primeSignMeasure

/-- The predecessor and the following L original vertices. -/
def vertexLabel (x L : ℕ) (v : Fin (L+1)) : ℕ :=
  if v.val=0 then x-1 else x+(v.val-1)

def vertexParityMap (x L : ℕ) : (Fin (L+1) → F₂) →ₗ[F₂] (ℕ →₀ F₂) :=
  Fintype.linearCombination F₂ (fun v ↦ parity (vertexLabel x L v))

/-- Zero total parity selects an even number of window vertices. -/
def evennessMap (L : ℕ) : (Fin (L+1) → F₂) →ₗ[F₂] F₂ where
  toFun w := ∑ v, w v
  map_add' w z := by simp only [Pi.add_apply,Finset.sum_add_distrib]
  map_smul' c w := by
    change (∑ v, c*w v)=c*∑ v,w v
    rw [Finset.mul_sum]

def evenParityMap (x L : ℕ) : LinearMap.ker (evennessMap L) →ₗ[F₂] (ℕ →₀ F₂) :=
  (vertexParityMap x L).comp (LinearMap.ker (evennessMap L)).subtype

/-- Effective even square classes, with actual local relations factored out. -/
def squareClassSpace (x L : ℕ) : Submodule F₂ (ℕ →₀ F₂) :=
  LinearMap.range (evenParityMap x L)

def windowValues (x L : ℕ) : Finset ℕ := univ.image (vertexLabel x L)

def normalizedWindow (c x L : ℕ) : Finset ℕ :=
  (windowValues x L).image (fun n ↦ c*n)

def normalizedUnion (a b x y L : ℕ) : Finset ℕ :=
  normalizedWindow b x L ∪ normalizedWindow a y L

/-- Every normalized value has a prime above H private to that value. -/
def PrivateAbove (H : ℝ) (S : Finset ℕ) : Prop :=
  ∀ n∈S, ∃ p : ℕ, Nat.Prime p ∧ H<(p : ℝ) ∧ parity n p≠0 ∧
    ∀ m∈S,m≠n → parity m p=0

def Leading (a b : ℕ) : Prop := (a=2 ∧ b=3) ∨ (a=3 ∧ b=4)

/-- The original arithmetic good-edge predicate, including dependence. -/
def GoodEdge (H : ℝ) (N L x y : ℕ) : Prop :=
  x∈ground N ∧ y∈ground N ∧ x<y ∧ 0<jointRate L {x,y} ∧
    ¬Disjoint (squareClassSpace x L) (squareClassSpace y L) ∧
      ∃ a b : ℕ, Leading a b ∧ PrivateAbove H (normalizedUnion a b x y L)

def goodEdges (H : ℝ) (N L : ℕ) : Finset (Finset ℕ) :=
  (((ground N) ×ˢ (ground N)).filter (fun xy ↦ GoodEdge H N L xy.1 xy.2)).image
    (fun xy ↦ ({xy.1,xy.2} : Finset ℕ))

/-- The actual total pair intensity incident to one original site. -/
def incidence (H : ℝ) (N L x : ℕ) : ℝ :=
  ∑ e ∈ goodEdges H N L, if x∈e then jointRate L e else 0

abbrev Channel (N L : ℕ) :=
  ↥(ground N) ⊕ ↥(goodEdges (8*(L+1) : ℕ) N L)

/-- Nonnegative rates are bundled only after their arithmetic positivity proof. -/
def arrivalRate (N L : ℕ)
    (hp : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x) :
    Channel N L → ℝ≥0
  | Sum.inl x => ⟨(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x.val,hp x.val x.property⟩
  | Sum.inr e => ⟨jointRate L e.val,by
      apply integral_nonneg
      intro ω
      exact prod_nonneg fun x _ ↦ by split <;> norm_num⟩

/-- Independent single-site and pair arrivals on a concrete product space. -/
def arrivalMeasure (N L : ℕ)
    (hp : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x) :
    Measure (Channel N L → ℕ) := Measure.pi (fun a ↦ poissonMeasure (arrivalRate N L hp a))

/-- Each original site receives its own arrival and the incident pair arrivals. -/
def field (N L : ℕ) (ω : Channel N L → ℕ) (x : ground N) : ℕ :=
  ω (Sum.inl x)+∑ e : goodEdges (8*(L+1) : ℕ) N L,
    if x.val∈e.val then ω (Sum.inr e) else 0

/-- The actual unsigned field on the literal original grid. -/
def sourceMass (N L : ℕ) (z : ground N → ℕ) : ℝ :=
  primeSignMeasure.real {ω | ∀ x : ground N, (startIndicator x.val L ω).toNat=z x}

/-- Original arithmetic single rates are positive uniformly over every cutoff. -/
theorem positive_single_rates (C : ℝ) :
    ∃ N₀ : ℕ, 3≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2|≤C → ∀ H : ℝ, ∀ x : ℕ,
      0<(2^L : ℝ)⁻¹-incidence H N L x := by
  sorry

/-- The full original weighted grid law for every independent Poisson realization. -/
theorem weighted_original_grid (C ε : ℝ) (hε : 0<ε) :
    ∀ j : ℕ, ∃ N₀ : ℕ, 10≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2|≤C →
      ∃ hp : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Channel N L → Ω → ℕ),
        (∀ a, HasLaw (X a) (poissonMeasure (arrivalRate N L hp a)) P) → iIndepFun X P →
        let error := fun z : ground N → ℕ ↦ (1+∑ x : ground N,(z x : ℝ))^j *
          |sourceMass N L z-P.real {ω | ∀ x : ground N,field N L (fun a ↦ X a ω) x=z x}|
        Summable error ∧ (∑' z : ground N → ℕ,error z)≤(N : ℝ)^(-4/5+ε) := by
  sorry

/-- The same convergent comparison on the explicit product Poisson space. -/
theorem canonical_weighted_grid (C ε : ℝ) (hε : 0<ε) :
    ∀ j : ℕ, ∃ N₀ : ℕ, 10≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2|≤C →
      ∃ hp : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x,
      let error := fun z : ground N → ℕ ↦ (1+∑ x : ground N,(z x : ℝ))^j *
        |sourceMass N L z-(arrivalMeasure N L hp).real
          {ω | ∀ x : ground N,field N L ω x=z x}|
      Summable error ∧ (∑' z : ground N → ℕ,error z)≤(N : ℝ)^(-4/5+ε) := by
  sorry

end PaperP1Registry.PositionalField
