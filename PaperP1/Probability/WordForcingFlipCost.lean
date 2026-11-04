module

public import PaperP1.Probability.BinaryForcingFlip

/-! # Actual uniform signed/unsigned target-word costs of a single-bit flip

These are finite lower mechanisms used after a clean arithmetic pair has
been constructed. The independence is realized by nested finite averages.
No arithmetic host count or asymptotic forcing lower bound is asserted.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WordForcingFlipCost

open Finset PaperP1.Algebra PaperP1.Probability PaperP1.UniformFubini PaperP1.Arithmetic
  PaperP1.BinaryForcingFlip

local instance wordForcingFlipCostDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

def singleFlip (i : ι) : (ι → F₂) ≃ (ι → F₂) :=
  Equiv.addRight (Pi.single i (1 : F₂) : ι → F₂)

def signedCost (P : FiniteProbability Ω) (δ : Ω → F₂) (b : ι → F₂) (i : ι) : ℝ :=
  finiteExpectation P.weight (fun ω ↦ average (fun v : ι → F₂ ↦
    |(if v = b then (1 : ℝ) else 0) -
      (if (if δ ω = 1 then singleFlip i v else v) = b then 1 else 0)|))

def unsignedCost (P : FiniteProbability Ω) (δ : Ω → F₂) (b : ι → F₂) (i : ι) : ℝ :=
  finiteExpectation P.weight (fun ω ↦ average (fun v : ι → F₂ ↦
    |(if orbit b v then (1 : ℝ) else 0) -
      (if orbit b (if δ ω = 1 then singleFlip i v else v) then 1 else 0)|))

omit [Fintype Ω] in
theorem singleton_probability (b : ι → F₂) :
    average (fun v : ι → F₂ ↦ if v = b then (1 : ℝ) else 0) =
      (2 ^ Fintype.card ι : ℝ)⁻¹ := by
  simp [average, uniformFiniteExpectation_eq]

omit [Fintype Ω] in
theorem orbit_probability (b : ι → F₂) (anchor : ι) :
    average (fun v : ι → F₂ ↦ if orbit b v then (1 : ℝ) else 0) =
      (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ := by
  have hi : Function.Injective (fun s : F₂ ↦ fun i ↦ b i + s) := by
    intro s t he
    exact add_left_cancel (congrFun he anchor)
  have he : (univ.filter (orbit b) : Finset (ι → F₂)) =
      (univ : Finset F₂).image (fun s ↦ fun i ↦ b i + s) := by
    ext v
    simp [orbit, eq_comm]
  have hc : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨anchor⟩
  have hp : (2 ^ Fintype.card ι : ℝ) = 2 ^ (Fintype.card ι - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hc]
  rw [average, uniformFiniteExpectation_indicator, he, card_image_of_injective _ hi,
    card_univ, ZMod.card, Fintype.card_fun, ZMod.card]
  push_cast
  rw [hp]
  field_simp

omit [Fintype Ω] [Fintype ι] in
theorem singleton_disjoint (b : ι → F₂) (i : ι) (u : ι → F₂) (hu : u = b) :
    singleFlip i u ≠ b := by
  subst u
  intro h
  have hi := congrFun h i
  change b i + (Pi.single i (1 : F₂) : ι → F₂) i = b i at hi
  rw [Pi.single_eq_same] at hi
  have hz : (1 : F₂) = 0 := add_left_cancel (by simpa only [add_zero] using hi)
  exact one_ne_zero hz

theorem signedCost_eq (P : FiniteProbability Ω) (δ : Ω → F₂) (b : ι → F₂) (i : ι) :
    signedCost P δ b i = 2 * finiteExpectation P.weight (fun ω ↦ bitIndicator (δ ω)) *
      (2 ^ Fintype.card ι : ℝ)⁻¹ := by
  have h := independent_flip_cost P δ (singleFlip i) (fun v ↦ v = b) (singleton_disjoint b i)
  exact h.trans (congrArg (fun t : ℝ ↦
    2 * finiteExpectation P.weight (fun ω ↦ bitIndicator (δ ω)) * t) (singleton_probability b))

theorem unsignedCost_eq (P : FiniteProbability Ω) (δ : Ω → F₂) (b : ι → F₂)
    (i j : ι) (hji : j ≠ i) :
    unsignedCost P δ b i = 2 * finiteExpectation P.weight (fun ω ↦ bitIndicator (δ ω)) *
      (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ := by
  rw [unsignedCost, independent_flip_cost P δ (singleFlip i) (orbit b)
    (fun u hu ↦ orbit_disjoint_single_flip b i j hji u hu), orbit_probability b i]

theorem fair_signed_cost (P : FiniteProbability Ω) (δ : Ω → F₂) (b : ι → F₂) (i : ι)
    (hfair : finiteExpectation P.weight (fun ω ↦ bitIndicator (δ ω)) = 1 / 2) :
    signedCost P δ b i = (2 ^ Fintype.card ι : ℝ)⁻¹ := by
  rw [signedCost_eq, hfair]
  ring

theorem fair_unsigned_cost (P : FiniteProbability Ω) (δ : Ω → F₂) (b : ι → F₂)
    (i j : ι) (hji : j ≠ i)
    (hfair : finiteExpectation P.weight (fun ω ↦ bitIndicator (δ ω)) = 1 / 2) :
    unsignedCost P δ b i = (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ := by
  rw [unsignedCost_eq P δ b i j hji, hfair]
  ring

theorem quarter_unsigned_cost (P : FiniteProbability Ω) (δ : Ω → F₂) (b : ι → F₂)
    (i j : ι) (hji : j ≠ i)
    (hquarter : 1 / 4 ≤ finiteExpectation P.weight (fun ω ↦ bitIndicator (δ ω))) :
    (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ / 2 ≤ unsignedCost P δ b i := by
  rw [unsignedCost_eq P δ b i j hji]
  have hp : (0 : ℝ) ≤ (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ := by positivity
  nlinarith only [hquarter, hp]

/-- The factor1/2 local obstruction holds without marginal fairness of `ξ`. -/
theorem two_candidate_cost_lower (P : FiniteProbability Ω) (X Y ξ : Ω → F₂) (b c : F₂)
    (hfair : finiteExpectation P.weight (fun ω ↦ bitIndicator (X ω + Y ω + b + c)) = 1 / 2)
    (target : ι → F₂) (i j : ι) (hji : j ≠ i) :
    ((2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ / 2 ≤
      unsignedCost P (fun ω ↦ X ω + b + ξ ω) target i) ∨
    ((2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ / 2 ≤
      unsignedCost P (fun ω ↦ Y ω + c + ξ ω) target i) := by
  rcases one_candidate_quarter P X Y ξ b c hfair with h | h
  · exact Or.inl (quarter_unsigned_cost P _ target i j hji h)
  · exact Or.inr (quarter_unsigned_cost P _ target i j hji h)

omit [Fintype Ω] in
theorem specified_signed_source_cost {κ : Type*} [Fintype κ] [DecidableEq κ]
    (source : κ → F₂) (k : κ) (target : ι → F₂) (i : ι) :
    signedCost (uniformFiniteProbability (κ → F₂)) (fun u ↦ u k - source k) target i =
      (2 ^ Fintype.card ι : ℝ)⁻¹ :=
  fair_signed_cost _ _ target i (uniform_single_fair k (source k))

omit [Fintype Ω] in
theorem specified_anchored_source_cost {κ : Type*} [Fintype κ] [DecidableEq κ]
    (source : κ → F₂) (k anchor : κ) (hne : anchor ≠ k)
    (target : ι → F₂) (i j : ι) (hji : j ≠ i) :
    unsignedCost (uniformFiniteProbability (κ → F₂))
      (fun u ↦ u k - (source k + (u anchor - source anchor))) target i =
        (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ :=
  fair_unsigned_cost _ _ target i j hji (anchored_uniform_flip_fair k anchor hne source)

omit [Fintype Ω] in
theorem arbitrary_orientation_source_lower {κ : Type*} [Fintype κ] [DecidableEq κ]
    (source : κ → F₂) (k l : κ) (hlk : l ≠ k) (ξ : (κ → F₂) → F₂)
    (target : ι → F₂) (i j : ι) (hji : j ≠ i) :
    ((2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ / 2 ≤
      unsignedCost (uniformFiniteProbability (κ → F₂))
        (fun u ↦ u k + source k + ξ u) target i) ∨
    ((2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ / 2 ≤
      unsignedCost (uniformFiniteProbability (κ → F₂))
        (fun u ↦ u l + source l + ξ u) target i) := by
  apply two_candidate_cost_lower _ _ _ ξ (source k) (source l) _ target i j hji
  simpa only [add_assoc] using uniform_parity_fair k l hlk (source k + source l)

end PaperP1.WordForcingFlipCost
