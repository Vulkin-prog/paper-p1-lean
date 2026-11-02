module

public import PaperP1.Model.ColoredReplicaMass
public import PaperP1.Probability.CoordinateConditioning
public import PaperP1.Probability.FiniteObservationConditional
public import PaperP1.Model.RelativeSignIndependence

/-! # Actual infinite-measure conditional expectations given common small prime signs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallPrimeConditioning

open MeasureTheory PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.ColoredPrimeSamples
  PaperP1.UniformFubini PaperP1.Model.InfiniteRademacher PaperP1.ColoredReplicaMass
  PaperP1.RelativeSignIndependence PaperP1.Probability.InfiniteCylinderTransfer
  PaperP1.Probability.CylinderExpectations

local instance smallPrimeConditioningTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance smallPrimeConditioningMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance smallPrimeConditioningDecidable (P : Prop) : Decidable P := Classical.propDecidable P

abbrev smallPredicate (M Y : ℕ) : PrimeUpTo M → Prop := fun p ↦ p.val.val ≤ Y

abbrev smallBits (M Y : ℕ) (σ : SampleSpace M) : {p : PrimeUpTo M // p.val.val ≤ Y} → F₂ :=
  (CoordinateConditioning.split (smallPredicate M Y) σ).1

abbrev observation (M Y : ℕ) (ω : InfiniteSample) := smallBits M Y (restrictToFinite M ω)

abbrev filtration (M Y : ℕ) : MeasurableSpace InfiniteSample :=
  MeasurableSpace.comap (observation M Y) inferInstance

theorem glue_eq_merge (M Y : ℕ) (σ τ : SampleSpace M) :
    glue Y σ τ = CoordinateConditioning.merge (smallPredicate M Y) σ τ := by
  funext p
  rw [CoordinateConditioning.merge_apply]
  rfl

theorem block_average_merge {ι κ : Type*} {M : ℕ} (Y L : ℕ) (x : ι → ℕ)
    (color : ι → κ) (b : ι → Fin L → F₂) (k : κ) (σ : SampleSpace M) :
    blockProbability Y L x color b k σ =
      average (fun τ : SampleSpace M ↦
        if ∀ i, color i = k → startSystem M (x i) L
          (CoordinateConditioning.merge (smallPredicate M Y) σ τ) = b i then 1 else 0) := by
  unfold blockProbability
  simp_rw [glue_eq_merge]

theorem block_condExp {ι κ : Type*} {M : ℕ} (Y L : ℕ) (x : ι → ℕ)
    (color : ι → κ) (b : ι → Fin L → F₂) (k : κ) (hcut : ∀ i, x i + L ≤ M) :
    (fun ω : InfiniteSample ↦ blockProbability Y L x color b k (restrictToFinite M ω)) =ᵐ[infiniteRademacherMeasure]
      condExp (filtration M Y) infiniteRademacherMeasure
        (fun ω ↦ if ∀ i, color i = k → infiniteStartBits (x i) L ω = b i then (1 : ℝ) else 0) := by
  classical
  let e := CoordinateConditioning.split (smallPredicate M Y) (Ω := F₂)
  let Z := fun ω : InfiniteSample ↦ e (restrictToFinite M ω)
  let f := fun p ↦ if ∀ i, color i = k → startSystem M (x i) L (e.symm p) = b i then (1 : ℝ) else 0
  have hZ : Measurable Z := Measurable.of_discrete.comp (measurable_restrictToFinite M)
  have htransport (g : ({p : PrimeUpTo M // p.val.val ≤ Y} → F₂) ×
      ({p : PrimeUpTo M // ¬p.val.val ≤ Y} → F₂) → ℝ) :
      (∫ ω, g (Z ω) ∂infiniteRademacherMeasure) = average g := by
    rw [infiniteCylinder_integral M (fun σ ↦ g (e σ))]
    exact UniformFubini.equiv e g
  have h := FiniteObservationConditional.mean_is_condExp infiniteRademacherMeasure Z hZ htransport f
  have hleft (ω : InfiniteSample) : blockProbability Y L x color b k (restrictToFinite M ω) =
      average (fun ν ↦ f ((Z ω).1, ν)) := by
    rw [block_average_merge]
    exact CoordinateConditioning.averaging_merge (smallPredicate M Y)
      (fun σ : SampleSpace M ↦ if ∀ i, color i = k → startSystem M (x i) L σ = b i then (1 : ℝ) else 0)
      (restrictToFinite M ω)
  have hright (ω : InfiniteSample) : f (Z ω) =
      if ∀ i, color i = k → infiniteStartBits (x i) L ω = b i then (1 : ℝ) else 0 := by
    dsimp [f, Z]
    simp_rw [Equiv.symm_apply_apply, startSystem_restrict_eq (hcut _)]
  simp_rw [hleft]
  simpa only [hright] using h

end PaperP1.SmallPrimeConditioning
