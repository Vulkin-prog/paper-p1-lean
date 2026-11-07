module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring
public import PaperP1.Analysis.UnconditionalPrintedAnchorObstruction

/-! # Actual arithmetic private forcing and universal anchor obstructions
The independent finite prime signs, retained population, arithmetic pivots,
actual forcing and every offsite cost are explicit Mathlib definitions.
The two T19.17 coefficients and the arbitrary independent auxiliary law are
preserved. Selected model foundations are adapted through P1 from Paper C,
commit b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0; see docs/PAPER_C_REUSE.md.
Only the four selected Challenge theorem holes are deliberate placeholders.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1Registry.PrivateObstruction
open Finset MeasureTheory
open scoped Classical
abbrev F₂ := ZMod 2
local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Prime coordinates up to the inclusive cutoff M. -/
def PrimeUpTo (M : ℕ) := {p : Fin (M+1) // Nat.Prime p.val}
instance primeFintype (M : ℕ) : Fintype (PrimeUpTo M) := Subtype.fintype _
instance primeDecidableEq (M : ℕ) : DecidableEq (PrimeUpTo M) := Classical.decEq _
abbrev Sample (M : ℕ) := PrimeUpTo M → F₂

def parity (n : ℕ) : ℕ →₀ F₂ :=
  n.factorization.mapRange (fun e : ℕ ↦ (e : F₂)) (by simp)

def value {M : ℕ} (ω : Sample M) (n : ℕ) : F₂ :=
  ∑ p : PrimeUpTo M, ω p * parity n p.val.val

def rawWord {M K : ℕ} (j : ℕ) (ω : Sample M) : Fin (K+1) → F₂ :=
  fun i ↦ value ω (j+i.val)

/-- The largest prime with odd valuation, including the prime 2; 1 for squares. -/
def largestOddPrime (n : ℕ) : ℕ :=
  max 1 ((n.factorization.mapRange (fun e : ℕ ↦ e%2) (by simp)).support.sup id)

def boundaryBlock (N : ℕ) : Finset ℕ := (Ico N (2*N)).image (fun x ↦ x-1)
def smallVertices (j B Y : ℕ) : Finset (Fin B) :=
  univ.filter fun i ↦ largestOddPrime (j+i.val) ≤ Y

/-- At most one small pivot in the entire maximal support. -/
def retained (N B Y : ℕ) : Finset ℕ :=
  (boundaryBlock N).filter fun j ↦ (smallVertices j B Y).card ≤ 1

def badAt (N B Z : ℕ) (i : Fin B) : Finset ℕ :=
  (Ico N (2*N)).filter fun x ↦ largestOddPrime (x-1+i.val) ≤ Z

def fullGood (N B Z : ℕ) : Finset ℕ :=
  boundaryBlock N \ ((univ.biUnion (badAt N B Z)).image (fun x ↦ x-1))

def cutoff (N : ℕ) : ℕ := ⌊(Real.log (N : ℝ))^5⌋₊
abbrev Free {K : ℕ} (anchor : Fin (K+1)) := {i : Fin (K+1) // i ≠ anchor}

/-- Pure arithmetic admissibility, before sampling any signs. -/
structure WindowData (M j K Y : ℕ) (anchor : Fin (K+1)) : Prop where
  boundary_pos : 0 < j
  support_cutoff : j+(K+1) ≤ M+1
  small_pos : 1 ≤ Y
  word_width : K+1 ≤ Y
  good : ∀ i : Free anchor, Y < largestOddPrime (j+i.val.val)

structure PrivateData (M Y K : ℕ) (G : Finset ℕ) (anchor : G → Fin (K+1)) : Prop where
  window : ∀ j : G, WindowData M j.val K Y (anchor j)

structure HybridData (M Y K : ℕ) (G Good : Finset ℕ) (anchor : G → Fin (K+1)) : Prop where
  anchored : PrivateData M Y K G anchor
  good : ∀ j : G, j.val ∈ Good → ∀ i : Fin (K+1), Y < largestOddPrime (j.val+i.val)

/-- Uniform independent prime signs, expressed as a finite normalized sum. -/
def average {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  ∑ ω, (Fintype.card Ω : ℝ)⁻¹*f ω

def orbit {K : ℕ} (b u : Fin (K+1) → F₂) : Prop := ∃ s : F₂, u=fun i ↦ b i+s

def indicator {M K : ℕ} {G : Finset ℕ} (b : Fin (K+1) → F₂) (j : G) (ω : Sample M) : Bool :=
  decide (orbit b (rawWord j.val ω))

def indicatorValue (b : Bool) : ℝ := if b then 1 else 0

/-- Only the actual nonanchor private primes are modified. -/
def force {M K : ℕ} {G : Finset ℕ} (anchor : G → Fin (K+1))
    (q : ∀ j : G, Free (anchor j) → PrimeUpTo M) (b : Fin (K+1) → F₂)
    (j : G) (ω : Sample M) : Sample M :=
  ω + ∑ i : Free (anchor j),
    (b i.val-b (anchor j)-value ω ((j.val+i.val.val)*(j.val+(anchor j).val))) • Pi.single (q j i) 1

def offsite {M K : ℕ} {G : Finset ℕ} (anchor : G → Fin (K+1))
    (q : ∀ j : G, Free (anchor j) → PrimeUpTo M) (b : Fin (K+1) → F₂) : ℝ :=
  ∑ j : G, average (fun ω : Sample M ↦ indicatorValue (indicator b j ω)) *
    average (fun ω : Sample M ↦ ∑ k ∈ (univ : Finset G).erase j,
      |indicatorValue (indicator b k ω)-indicatorValue (indicator b k (force anchor q b j ω))|)

/-- The exact printed lower scale, including the offset coefficient. -/
def nominal (N L i : ℕ) (a : ℝ) : ℝ :=
  (2^(2*i) : ℝ)⁻¹*((N : ℝ)*(2^L : ℝ)⁻¹)^2*(N : ℝ)^(-a)

def randomizedOffsite {M K : ℕ} {G : Finset ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (b : Fin (K+1) → F₂) (F : G → Sample M → Ξ → Sample M) : ℝ :=
  ∑ j : G, (2^K : ℝ)⁻¹*average (fun ω : Sample M ↦
    ∫ ξ, ∑ k ∈ (univ : Finset G).erase j,
      |indicatorValue (indicator b k ω)-indicatorValue (indicator b k (F j ω ξ))| ∂μ)

theorem parity_eq (n : ℕ) : parity n = PaperP1.Arithmetic.parityVec n := by rfl

theorem value_eq {M : ℕ} (ω : Sample M) (n : ℕ) : value ω n = PaperP1.Model.valueBit ω n := by rfl

theorem rawWord_eq {M K : ℕ} (j : ℕ) (ω : Sample M) :
    rawWord (K:=K) j ω = PaperP1.PrivateValueSystem.valueSystem M (fun i : Fin (K+1) ↦ j+i.val) ω := by rfl

theorem largest_eq (n : ℕ) : largestOddPrime n = PaperP1.OddPrimePivot.largestOddPrime n := by rfl

theorem retained_eq (N B Y : ℕ) : retained N B Y = PaperP1.AnchoredDyadicField.retainedBoundaries N B Y := by rfl

theorem good_eq (N B Z : ℕ) : fullGood N B Z = PaperP1.RandomizedDyadicHybridField.fullGood N B Z := by rfl

theorem toSource {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : PrivateData M Y K G anchor) : PaperP1.AnchoredPrivateField.Data M Y K G anchor where
  window := fun j ↦ ⟨(A.window j).boundary_pos,(A.window j).support_cutoff,
    (A.window j).small_pos,(A.window j).word_width,(A.window j).good⟩

theorem hybridToSource {M Y K : ℕ} {G Good : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : HybridData M Y K G Good anchor) : PaperP1.RandomizedHybridField.Data M Y K G Good anchor where
  anchored := toSource A.anchored
  good := A.good

theorem average_eq {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    average f = PaperP1.UniformFubini.average f := by rfl

theorem indicator_eq {M K : ℕ} {G : Finset ℕ} (b : Fin (K+1) → F₂) (j : G) (ω : Sample M) :
    indicator b j ω = PaperP1.AnchoredPrivateField.indicator b j ω := by rfl

theorem force_eq {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : PrivateData M Y K G anchor)
    (q : ∀ j : G, Free (anchor j) → PrimeUpTo M)
    (hq : ∀ j i, (q j i).val.val=largestOddPrime (j.val+i.val.val))
    (b : Fin (K+1) → F₂) (j : G) (ω : Sample M) :
    force anchor q b j ω = PaperP1.AnchoredPrivateField.force (toSource A) b j ω := by
  have he : q j=PaperP1.AnchoredWindowForcing.pivots ((toSource A).window j) := by
    funext i
    apply Subtype.ext
    apply Fin.ext
    exact hq j i
  unfold force PaperP1.AnchoredPrivateField.force PaperP1.AnchoredWindowForcing.force
    PaperP1.AnchoredPrivateForcing.force PaperP1.PrivatePrimeForcing.forceWord
    PaperP1.PrivatePrimeForcing.liftBlock
  rw [he]
  rfl

theorem offsite_eq {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : PrivateData M Y K G anchor)
    (q : ∀ j : G, Free (anchor j) → PrimeUpTo M)
    (hq : ∀ j i, (q j i).val.val=largestOddPrime (j.val+i.val.val)) (b : Fin (K+1) → F₂) :
    offsite anchor q b = PaperP1.AnchoredPrivateField.offsite (toSource A) b := by
  simp only [offsite,indicator_eq,force_eq A q hq]
  rfl

theorem randomizedOffsite_eq {M K : ℕ} {G : Finset ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (b : Fin (K+1) → F₂) (F : G → Sample M → Ξ → Sample M) :
    randomizedOffsite μ b F = PaperP1.PrivateForcingMeasureObservation.offsite μ b F := by rfl

theorem fromSource {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : PaperP1.AnchoredPrivateField.Data M Y K G anchor) : PrivateData M Y K G anchor where
  window := fun j ↦ ⟨(A.window j).boundary_pos,(A.window j).cutoff,
    (A.window j).small_pos,(A.window j).word_width,(A.window j).good⟩

theorem hybridFromSource {M Y K : ℕ} {G Good : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : PaperP1.RandomizedHybridField.Data M Y K G Good anchor) : HybridData M Y K G Good anchor where
  anchored := fromSource A.anchored
  good := A.good

/-- The retained population admits anchors and actual private prime choices.
Every admissible arithmetic anchor rule gives such a field. -/
theorem admissible_fields {N B Y K M : ℕ} (hN : 2 ≤ N) (hKB : K+1 ≤ B)
    (hBY : B ≤ Y) (hM : 2*N+B ≤ M) :
    (∃ anchor : retained N B Y → Fin (K+1), ∀ j i,
      largestOddPrime (j.val+i.val) ≤ Y → i=anchor j) ∧
    ∀ anchor : retained N B Y → Fin (K+1),
      (∀ j i, largestOddPrime (j.val+i.val) ≤ Y → i=anchor j) →
      PrivateData M Y K (retained N B Y) anchor ∧
      (∃ q : ∀ j : retained N B Y, Free (anchor j) → PrimeUpTo M,
        ∀ j i, (q j i).val.val=largestOddPrime (j.val+i.val.val)) ∧
      ∀ Z : ℕ, Y ≤ Z →
        HybridData M Y K (retained N B Y) (fullGood N B Z) anchor ∧
        ∃ q : ∀ j : retained N B Y, j.val ∈ fullGood N B Z → Fin (K+1) → PrimeUpTo M,
          ∀ j hj i, (q j hj i).val.val=largestOddPrime (j.val+i.val) :=
by
  constructor
  · exact PaperP1.AnchoredDyadicField.exists_anchor_rule hKB
  · intro anchor hrule
    have AS := PaperP1.AnchoredDyadicField.data hN hKB hBY hM anchor hrule
    refine ⟨fromSource AS,⟨(fun j ↦ PaperP1.AnchoredWindowForcing.pivots (AS.window j)),?_⟩,?_⟩
    · intro j i
      rfl
    · intro Z hYZ
      have HS := PaperP1.RandomizedDyadicHybridField.data hN hKB hBY hYZ hM anchor hrule
      refine ⟨hybridFromSource HS,PaperP1.RandomizedHybridField.fullPivots HS,?_⟩
      intro j hj i
      rfl

/-- Full sample conditional law for every observable, with the arithmetic
anchor and every small prime preserved, and exact source-word orientation. -/
theorem conditional_forcing {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : PrivateData M Y K G anchor)
    (q : ∀ j : G, Free (anchor j) → PrimeUpTo M)
    (hq : ∀ j i, (q j i).val.val=largestOddPrime (j.val+i.val.val))
    (b : Fin (K+1) → F₂) (j : G) :
    (∀ f : Sample M → ℝ, average (fun ω ↦ f (force anchor q b j ω)) =
      average (fun ω ↦ if orbit b (rawWord j.val ω) then f ω else 0)/(2^K : ℝ)⁻¹) ∧
    ∀ ω : Sample M,
      value (force anchor q b j ω) (j.val+(anchor j).val)=value ω (j.val+(anchor j).val) ∧
      (∀ p : PrimeUpTo M, p.val.val ≤ Y → force anchor q b j ω p=ω p) ∧
      rawWord j.val (force anchor q b j ω)=
        fun i ↦ b i+(value ω (j.val+(anchor j).val)-b (anchor j)) :=
by
  have hforce := force_eq A q hq b j
  constructor
  · intro f
    simp only [hforce,average_eq]
    have hs := PaperP1.AnchoredWindowForcing.full_conditional ((toSource A).window j) b f
    simp only [Nat.add_sub_cancel] at hs
    refine hs.trans ?_
    congr 1
    apply PaperP1.UniformFubini.congr
    intro ω
    by_cases hp : orbit b (rawWord j.val ω)
    · have hex : ∃ s : F₂, PaperP1.PrivateValueSystem.valueSystem M
          (fun k : Fin (K+1) ↦ j.val+k.val) ω=(fun i ↦ b i+s) := hp
      rw [ite_eq_left hex,ite_eq_left hp]
    · have hex : ¬∃ s : F₂, PaperP1.PrivateValueSystem.valueSystem M
          (fun k : Fin (K+1) ↦ j.val+k.val) ω=(fun i ↦ b i+s) := hp
      rw [ite_eq_right hex,ite_eq_right hp]
  · intro ω
    simp only [hforce,value_eq]
    refine ⟨PaperP1.AnchoredWindowForcing.preserves_anchor ((toSource A).window j) b ω,?_,
      PaperP1.AnchoredWindowForcing.actual_orientation ((toSource A).window j) b ω⟩
    intro p hp
    exact congrFun (PaperP1.AnchoredWindowForcing.preserves_small ((toSource A).window j) b ω) ⟨p,hp⟩

/-- The complete deterministic printed T19.17 obstruction. One cutoff precedes
all maximal supports, both offsets, every arithmetic anchor and source word.
No census or analytic bound is assumed. -/
theorem deterministic_obstruction (C D a : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1/10) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E M : ℕ, ∀ i : Fin 2,
      ((L+E+2 : ℕ) : ℝ) ≤ D*Real.log N → 2*N+(L+E+2) ≤ M →
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∀ anchor : retained N (L+E+2) (2*(L+E+2)) → Fin (L+i.val+1),
      ∀ _field : PrivateData M (2*(L+E+2)) (L+i.val)
        (retained N (L+E+2) (2*(L+E+2))) anchor,
      ∀ q : ∀ j : retained N (L+E+2) (2*(L+E+2)), Free (anchor j) → PrimeUpTo M,
      (∀ j k, (q j k).val.val=largestOddPrime (j.val+k.val.val)) →
      ∀ b : Fin (L+i.val+1) → F₂, (1-η)*nominal N L i.val a ≤ offsite anchor q b :=
by
  obtain ⟨N₀,h⟩ := PaperP1.UnconditionalPrintedAnchorObstruction.companion_T19_17 C D a hD ha ha1 η hη
  refine ⟨N₀,?_⟩
  intro N hN L E M i hwidth hM hband anchor A q hq b
  rw [offsite_eq A q hq b]
  exact h N hN L E M i hwidth hM hband anchor (toSource A) b

/-- The complete randomized T19.17 obstruction, with the exact extra one half.
The auxiliary probability space is arbitrary and independent of prime signs.
Orientations may depend on the source word and auxiliary sample. -/
theorem randomized_obstruction (C D a : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1/10) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E M : ℕ, ∀ i : Fin 2,
      ((L+E+2 : ℕ) : ℝ) ≤ D*Real.log N → 2*N+(L+E+2) ≤ M →
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∀ anchor : retained N (L+E+2) (2*(L+E+2)) → Fin (L+i.val+1),
      ∀ _field : HybridData M (2*(L+E+2)) (L+i.val)
        (retained N (L+E+2) (2*(L+E+2))) (fullGood N (L+E+2) (cutoff N)) anchor,
      ∀ q : ∀ j : retained N (L+E+2) (2*(L+E+2)),
        j.val ∈ fullGood N (L+E+2) (cutoff N) → Fin (L+i.val+1) → PrimeUpTo M,
      (∀ j hj k, (q j hj k).val.val=largestOddPrime (j.val+k.val)) →
      ∀ (Ξ : Type*) [MeasurableSpace Ξ], ∀ μ : Measure Ξ, ∀ [IsProbabilityMeasure μ],
      ∀ b : Fin (L+i.val+1) → F₂,
      ∀ g : retained N (L+E+2) (2*(L+E+2)) → (Fin (L+i.val+1) → F₂) → Ξ → F₂,
      ∀ F : retained N (L+E+2) (2*(L+E+2)) → Sample M → Ξ → Sample M,
      (∀ j u s, MeasurableSet {ξ : Ξ | g j u ξ=s}) →
      (∀ j ω r s, MeasurableSet {ξ : Ξ | F j ω ξ r=s}) →
      (∀ j, j.val ∈ fullGood N (L+E+2) (cutoff N) → ∀ ω ξ,
        rawWord j.val (F j ω ξ)=fun k ↦ b k+g j (rawWord j.val ω) ξ) →
      (∀ j, ∀ hj : j.val ∈ fullGood N (L+E+2) (cutoff N), ∀ ω ξ, ∀ r : PrimeUpTo M,
        (∀ k, r ≠ q j hj k) → F j ω ξ r=ω r) →
      (1-η)/2*nominal N L i.val a ≤ randomizedOffsite μ b F :=
by
  obtain ⟨N₀,h⟩ := PaperP1.UnconditionalPrintedAnchorObstruction.companion_T19_17_randomized C D a hD ha ha1 η hη
  refine ⟨N₀,?_⟩
  intro N hN L E M i hwidth hM hband anchor A q hq Ξ _ μ _ b g F hg hF hhit hout
  have heq : q = PaperP1.RandomizedHybridField.fullPivots (hybridToSource A) := by
    funext j hj k
    apply Subtype.ext
    apply Fin.ext
    exact hq j hj k
  rw [randomizedOffsite_eq]
  apply h N hN L E M i hwidth hM hband anchor (hybridToSource A) Ξ μ b g F hg hF hhit
  intro j hj ω ξ r hr
  apply hout j hj ω ξ r
  intro k
  rw [heq]
  exact hr k

end PaperP1Registry.PrivateObstruction
