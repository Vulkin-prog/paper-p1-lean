module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance

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


theorem exact_marginals (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e) (x : G) :
    ∃ r : ℝ≥0,(r : ℝ)=p x.val ∧
      HasLaw (fun ω ↦ field G E ω x) (poissonMeasure r) (arrivalMeasure G E p q hp hq) ∧
      ∀ j : ℕ,Integrable (fun ω ↦ ((field G E ω x).descFactorial j : ℝ))
        (arrivalMeasure G E p q hp hq) ∧
        (∫ ω,((field G E ω x).descFactorial j : ℝ) ∂arrivalMeasure G E p q hp hq)=p x.val^j := by
  sorry

theorem covariance_matrix (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e)
    (hE : ∀ e∈E,e.card=2) (x y : G) :
    cov[fun ω ↦ (field G E ω x : ℝ),fun ω ↦ (field G E ω y : ℝ);
      arrivalMeasure G E p q hp hq] =
      if x=y then p x.val else if {x.val,y.val}∈E then q {x.val,y.val} else 0 := by
  sorry

theorem pair_independence (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e)
    (hE : ∀ e∈E,e.card=2) (x y : G) (hxy : x≠y) :
    IndepFun (fun ω ↦ field G E ω x) (fun ω ↦ field G E ω y)
      (arrivalMeasure G E p q hp hq) ↔ {x.val,y.val}∉E ∨ q {x.val,y.val}=0 := by
  sorry

theorem block_dependency (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e)
    (hE : ∀ e∈E,e.card=2) (A B : Finset G) (hAB : Disjoint A B) :
    IndepFun (block G E A) (block G E B) (arrivalMeasure G E p q hp hq) ↔
      ∀ x∈A,∀ y∈B,¬({x.val,y.val}∈E ∧ 0<q {x.val,y.val}) := by
  sorry


end PaperP1Registry.PoissonReference
