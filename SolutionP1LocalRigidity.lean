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
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Data.Int.Interval
public import PaperP1.Arithmetic.SplitProductBound
public import PaperP1.Diophantine.UniformQuadraticCount
public import PaperP1.Model.RelativeSignIndependence

/-! # Uniform local arithmetic rigidity
The split-product and quadratic counts retain the degree and coefficient
uniformity of companion T1.1 and T1.2. The actual even square-relation
code, Griesmer budget, logarithmic ranks and independent relative prime
signs spell out main lemma 2.1. Prime-sign and Pell foundations are
adapted through P1 from Paper C commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0.
Five selected Challenge holes are deliberate statement placeholders.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1Registry.LocalRigidity
open Finset MeasureTheory
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

/-- Every even square relation in the literal B-vertex window. -/
def windowParityMap (U B : ℕ) : (Fin B → F₂) →ₗ[F₂] (ℕ →₀ F₂) :=
  Fintype.linearCombination F₂ (fun i ↦ parity (U+i.val))

def windowEvennessMap (B : ℕ) : (Fin B → F₂) →ₗ[F₂] F₂ :=
  Fintype.linearCombination F₂ (fun _ ↦ 1)

def relationCode (U B : ℕ) : Submodule F₂ (Fin B → F₂) :=
  LinearMap.ker (windowParityMap U B) ⊓ LinearMap.ker (windowEvennessMap B)

def relationRank (U B : ℕ) : ℕ := Module.finrank F₂ (relationCode U B)

def distance (U B : ℕ) : ℕ := ⌈Real.log U/Real.log (64*(B : ℝ))⌉₊

/-- Positive integer solutions of the literal equation, including both height endpoints. -/
def positiveSolutions (a b : ℕ) (h : ℤ) (H : ℕ) : Finset (ℤ×ℤ) :=
  ((Icc 1 (H : ℤ)) ×ˢ Icc 1 (H : ℤ)).filter fun z ↦
    (a : ℤ)*z.1^2-(b : ℤ)*z.2^2=h

def randomValue (ω : Sample) (n : ℕ) : ℤ := if valueBit ω n=0 then 1 else -1

/-- The reference vertex is U+1; all the other B-1 vertices occur exactly once. -/
def relativeVertex (U B : ℕ) (i : Fin (B-1)) : ℕ :=
  if i.val=0 then U else U+1+i.val

def relativeSign (U B : ℕ) (i : Fin (B-1)) (ω : Sample) : ℤ :=
  randomValue ω (relativeVertex U B i)*randomValue ω (U+1)

def relativeBits (U B : ℕ) (ω : Sample) (i : Fin (B-1)) : F₂ :=
  if i.val=0 then valueBit ω U+valueBit ω (U+1)
  else valueBit ω (U+1)+valueBit ω (U+1+i.val)

theorem parity_eq (n : ℕ) : parity n=PaperP1.Arithmetic.parityVec n := by rfl

theorem relationCode_eq (U B : ℕ) : relationCode U B=
    PaperP1.WindowRelationCode.windowRelationCode U B := by rfl

theorem relationRank_eq (U B : ℕ) : relationRank U B=
    Module.finrank F₂ (PaperP1.WindowRelationCode.windowRelationCode U B) := by rfl

theorem distance_eq (U B : ℕ) : distance U B=PaperP1.LocalRigidityCode.rungeDistance U B := by rfl

theorem positiveSolutions_eq (a b : ℕ) (h : ℤ) (H : ℕ) : positiveSolutions a b h H=
    PaperP1.UniformQuadraticCount.positiveQuadraticSolutions a b h H := by
  ext z
  simp only [positiveSolutions,PaperP1.UniformQuadraticCount.positiveQuadraticSolutions,
    Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,PaperP1.PellInput.pellEquation]

theorem relativeBits_eq (U B : ℕ) : relativeBits U B=
    PaperP1.RelativeSignIndependence.infiniteStartBits (U+1) (B-1) := by
  funext ω i
  simp only [relativeBits,PaperP1.RelativeSignIndependence.infiniteStartBits,Nat.add_sub_cancel]
  rfl

theorem relativeSign_eq (U B : ℕ) : relativeSign U B=
    PaperP1.RelativeSignIndependence.relativeSign (U+1) (B-1) := by
  funext i ω
  simp only [relativeSign,relativeVertex,randomValue,
    PaperP1.RelativeSignIndependence.relativeSign,PaperP1.RelativeSignIndependence.relativeVertex,
    PaperP1.Model.InfiniteRademacher.infiniteRandomValue,PaperP1.Model.phase,Nat.add_sub_cancel]
  rfl

theorem primeSignMeasure_eq : primeSignMeasure=
    PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure := by rfl

/-- Uniform in every even degree, with the original constant 64. -/
theorem split_product_bound {k : ℕ} (hk : 1≤k) {R : ℝ} (hR : 1≤R)
    {U : ℤ} (hU : 2*R≤(U : ℝ)) (γ : Fin (2*k) → ℤ)
    (hγ : ∀ i, |(γ i : ℝ)|≤R) (hinj : Function.Injective γ)
    (a : ℤ) (hsquare : ∏ i, (U+γ i)=a^2) :
    (U : ℝ)≤(64*R)^(2*k) := by
  exact PaperP1.SplitProductBound.uniform_split_product_real_radius hk hR hU γ hγ hinj a hsquare

/-- One cutoff precedes all coefficients, nonzero signs and positive solutions. -/
theorem uniform_quadratic_count (A₀ : ℝ) (hA₀ : 0<A₀) (ε : ℝ) (hε : 0<ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (a b : ℕ) (h : ℤ),
      0<a → 0<b → h≠0 → (a : ℝ)≤(N : ℝ)^A₀ → (b : ℝ)≤(N : ℝ)^A₀ →
      |(h : ℝ)|≤(N : ℝ)^A₀ →
      ((positiveSolutions a b h ⌊(N : ℝ)^A₀⌋₊).card : ℝ)≤(N : ℝ)^ε := by
  simpa only [positiveSolutions_eq] using
    PaperP1.UniformQuadraticCount.uniform_quadratic_equation_count A₀ hA₀ ε hε

/-- The real, untruncated Griesmer sum for the actual even square-relation code. -/
theorem finite_relative_griesmer {U B t : ℕ} (hB : 1≤B) (hU : 2*B≤U)
    (ht : t≤relationRank U B) :
    (∑ i ∈ range t, (⌈(distance U B : ℝ)/(2 : ℝ)^i⌉₊ : ℝ))-(t : ℝ)≤
      (Nat.primeCounting B : ℝ)+1 := by
  have h := PaperP1.WindowRelationCode.window_relation_griesmer_real hB hU
    (by simpa only [relationRank_eq] using ht)
  simpa only [distance_eq,PaperP1.LocalRigidityCode.primeCount_eq_primeCounting] using h

/-- Both exact original logarithmic regimes, with every base after the threshold. -/
theorem logarithmic_rank_regimes (a : ℝ) (ha : 0<a) :
    (∀ B : ℕ → ℕ,
      Asymptotics.IsLittleO Filter.atTop
        (fun N ↦ (B N : ℝ)-Real.log N/Real.log 2) (fun N ↦ Real.log (N : ℝ)) →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ U : ℕ, a*N≤(U : ℝ) → relationRank U (B N)≤1) ∧
    (∀ c : ℝ, 0<c → ∀ t : ℕ, c<2-(2 : ℝ)^(1-(t : ℤ)) → ∀ B : ℕ → ℕ,
      Asymptotics.IsEquivalent Filter.atTop (fun N ↦ (B N : ℝ))
        (fun N ↦ c*Real.log (N : ℝ)) →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ U : ℕ, a*N≤(U : ℝ) → relationRank U (B N)<t) := by
  constructor
  · intro B hB
    simpa only [relationRank_eq] using
      PaperP1.LocalRigidityRegimes.critical_relation_rank_le_one_of_error a ha B hB
  · intro c hc t hct B hB
    simpa only [relationRank_eq] using
      PaperP1.LocalRigidityRegimes.relation_rank_lt_of_length_asymptotic a c ha hc t hct B hB

/-- Actual fair product law of all relative bits, and exact independence of the signs. -/
theorem subcritical_relative_signs (a ε : ℝ) (ha : 0<a) (hε : 0<ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ U B : ℕ, 1≤B → a*N≤(U : ℝ) →
      (B : ℝ)≤(1-ε)*Real.log N →
      primeSignMeasure.map (relativeBits U B)=
        Measure.pi (fun _ : Fin (B-1) ↦ coordinateMeasure) ∧
      ProbabilityTheory.iIndepFun (relativeSign U B) primeSignMeasure := by
  obtain ⟨N₀,hN₀⟩ := PaperP1.UniformLocalRigidity.uniform_subcritical_relation_rank_zero a ε ha hε
  refine ⟨N₀, fun N hN U B hB hbase hwidth ↦ ?_⟩
  have hrel : Module.finrank F₂
      (PaperP1.WindowRelationCode.windowRelationCode (U+1-1) (B-1+1))=0 := by
    rw [Nat.add_sub_cancel,Nat.sub_add_cancel hB]
    exact hN₀ N hN U B hbase hwidth
  constructor
  · rw [relativeBits_eq,primeSignMeasure_eq]
    exact PaperP1.RelativeSignIndependence.map_infiniteStartBits_eq_pi (by omega : 0<U+1) hrel
  · rw [relativeSign_eq,primeSignMeasure_eq]
    exact PaperP1.RelativeSignIndependence.iIndepFun_relativeSigns (by omega : 0<U+1) hrel
end PaperP1Registry.LocalRigidity
