module

public import PaperP1.Model.SmallPrimeConditioning

/-! # The observed small-prime sigma algebra is independent of the larger cylinder cutoff -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallPrimeFiltration

open MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteRademacher
  PaperP1.SmallPrimeConditioning PaperP1.Probability.InfiniteCylinderTransfer

local instance smallPrimeFiltrationMeasurableF2 : MeasurableSpace F₂ := ⊤

abbrev primeFiltration (Y : ℕ) : MeasurableSpace InfiniteSample :=
  MeasurableSpace.comap (restrictToFinite Y) inferInstance

def raisePrime {Y M : ℕ} (hYM : Y ≤ M) (p : PrimeUpTo Y) : PrimeUpTo M :=
  ⟨⟨p.val.val, by have := p.val.isLt; omega⟩, p.property⟩

def lowerPrime (M Y : ℕ) (p : {q : PrimeUpTo M // q.val.val ≤ Y}) : PrimeUpTo Y :=
  ⟨⟨p.val.val.val, by have := p.property; omega⟩, p.val.property⟩

def liftSmall (M Y : ℕ) (σ : SampleSpace Y) : {p : PrimeUpTo M // p.val.val ≤ Y} → F₂ :=
  fun p ↦ σ (lowerPrime M Y p)

def lowerSmall {M Y : ℕ} (hYM : Y ≤ M) (σ : {p : PrimeUpTo M // p.val.val ≤ Y} → F₂) : SampleSpace Y :=
  fun p ↦ σ ⟨raisePrime hYM p, by have := p.val.isLt; change p.val.val ≤ Y; omega⟩

theorem observation_factor (M Y : ℕ) (ω : InfiniteSample) :
    observation M Y ω = liftSmall M Y (restrictToFinite Y ω) := rfl

theorem restriction_factor {M Y : ℕ} (hYM : Y ≤ M) (ω : InfiniteSample) :
    restrictToFinite Y ω = lowerSmall hYM (observation M Y ω) := rfl

theorem filtration_eq {M Y : ℕ} (hYM : Y ≤ M) : filtration M Y = primeFiltration Y := by
  apply le_antisymm
  · exact MeasurableSpace.comap_le_comap_of_eq_comp (liftSmall M Y) Measurable.of_discrete
      (funext (observation_factor M Y))
  · exact MeasurableSpace.comap_le_comap_of_eq_comp (lowerSmall hYM) Measurable.of_discrete
      (funext (restriction_factor hYM))

end PaperP1.SmallPrimeFiltration
