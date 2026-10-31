/-
Adapted in part from Vulkin-prog/paper-c-lean,
PaperC/Probability/InfiniteStartProbabilityTransfer.lean,
commit b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0.
Start/count restriction patterns are adapted to P1's Boolean indicators and
actual real-weight laws. Bochner centered-moment transport is new here.
-/
module

public import PaperP1.Model.StartFourier
public import PaperP1.Probability.CylinderExpectations
public import PaperP1.Probability.CenteredMeasureExpansion

/-!
# Actual run starts under the infinite prime-sign measure

Every supported start, centered moment and complete count law is transported
exactly to its finite cylinder. Individual actual marginals are retained.
The restriction and product-measure construction are checked Paper C ports;
this module connects them to the P1 real-valued probability development.
-/

@[expose] public noncomputable section

open scoped BigOperators
open MeasureTheory
open PaperP1.Arithmetic PaperP1.Algebra PaperP1.Probability
open PaperP1.Model PaperP1.Model.InfiniteRademacher
open PaperP1.Probability.InfiniteCylinderTransfer
open PaperP1.Probability.CylinderExpectations

namespace PaperP1.Model.InfiniteStarts

local instance : MeasurableSpace F₂ := ⊤
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def infiniteStartIndicator (x L : ℕ) (ω : InfiniteSample) : Bool :=
  decide (StartEvent (infiniteValueBit ω) x L)

theorem startIndicator_restrict_eq {M x L : ℕ} (ω : InfiniteSample) (hcut : x + L ≤ M) :
    startIndicator x L (restrictToFinite M ω) = infiniteStartIndicator x L ω := by
  have hiff := startAt_restrictToFinite_iff (M := M) (x := x) (L := L) ω hcut
  by_cases h : StartEvent (infiniteValueBit ω) x L
  · have hf : StartEvent (valueBit (restrictToFinite M ω)) x L := hiff.mpr h
    simp [startIndicator, infiniteStartIndicator, h, hf]
  · have hf : ¬StartEvent (valueBit (restrictToFinite M ω)) x L := mt hiff.mp h
    simp [startIndicator, infiniteStartIndicator, h, hf]

theorem measurable_infiniteStartIndicator (x L : ℕ) : Measurable (infiniteStartIndicator x L) := by
  have heq : infiniteStartIndicator x L =
      (startIndicator (M := x + L) x L) ∘ restrictToFinite (x + L) := by
    funext ω
    exact (startIndicator_restrict_eq ω le_rfl).symm
  rw [heq]
  exact Measurable.of_discrete.comp (measurable_restrictToFinite (x + L))

def infiniteMarginal (x L : ℕ) : ℝ :=
  ∫ ω, indicatorValue (infiniteStartIndicator x L ω) ∂infiniteRademacherMeasure

theorem infiniteMarginal_eq_finite {M x L : ℕ} (hcut : x + L ≤ M) :
    infiniteMarginal x L =
      exactMarginal (cylinderProbability M) (fun y => startIndicator y L) x := by
  unfold infiniteMarginal
  simp_rw [← startIndicator_restrict_eq (M := M) _ hcut]
  exact infiniteCylinder_integral M (fun σ => indicatorValue (startIndicator x L σ))

theorem infiniteMarginal_eq_dyadic {N L x : ℕ} (hx : x ∈ dyadicBlock N) :
    infiniteMarginal x L = dyadicMarginal N L x := by
  apply infiniteMarginal_eq_finite
  simp only [dyadicBlock, Finset.mem_Ico] at hx
  unfold dyadicCutoff
  omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def infiniteFamilyCenteredMoment (L : ℕ) (g : ι → ℕ) : ℝ :=
  ∫ ω, ∏ i, ((indicatorValue (infiniteStartIndicator (g i) L ω) : ℝ) -
    infiniteMarginal (g i) L) ∂infiniteRademacherMeasure

omit [DecidableEq ι] in
theorem infiniteFamilyCenteredMoment_eq_finite (M L : ℕ) (g : ι → ℕ)
    (hcut : ∀ i, g i + L ≤ M) :
    infiniteFamilyCenteredMoment L g = startFamilyCenteredMoment M L g := by
  unfold infiniteFamilyCenteredMoment startFamilyCenteredMoment
  simp_rw [infiniteMarginal_eq_finite (hcut _)]
  have hprod (ω : InfiniteSample) :
      (∏ i, ((indicatorValue (infiniteStartIndicator (g i) L ω) : ℝ) -
        exactMarginal (cylinderProbability M) (fun y => startIndicator y L) (g i))) =
      ∏ i, ((indicatorValue (startIndicator (g i) L (restrictToFinite M ω)) : ℝ) -
        exactMarginal (cylinderProbability M) (fun y => startIndicator y L) (g i)) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [startIndicator_restrict_eq ω (hcut i)]
  simp_rw [hprod]
  exact infiniteCylinder_integral M (fun σ =>
    ∏ i, ((indicatorValue (startIndicator (g i) L σ) : ℝ) -
      exactMarginal (cylinderProbability M) (fun y => startIndicator y L) (g i)))

def infiniteStartCount (G : Finset ℕ) (L : ℕ) (ω : InfiniteSample) : ℕ :=
  indicatorCount G (fun x => infiniteStartIndicator x L) ω

theorem infiniteStartCount_restrict (G : Finset ℕ) (L M : ℕ)
    (hcut : ∀ x ∈ G, x + L ≤ M) (ω : InfiniteSample) :
    indicatorCount G (fun x => startIndicator x L) (restrictToFinite M ω) =
      infiniteStartCount G L ω := by
  unfold indicatorCount infiniteStartCount
  apply Finset.sum_congr rfl
  intro x hx
  change (startIndicator x L (restrictToFinite M ω)).toNat =
    (infiniteStartIndicator x L ω).toNat
  rw [startIndicator_restrict_eq ω (hcut x hx)]

theorem measurable_infiniteStartCount (G : Finset ℕ) (L : ℕ) :
    Measurable (infiniteStartCount G L) := by
  let M := G.sup fun x => x + L
  have hcut : ∀ x ∈ G, x + L ≤ M := fun x hx => Finset.le_sup (f := fun x => x + L) hx
  have heq : infiniteStartCount G L =
      (indicatorCount G (fun x => startIndicator x L)) ∘ restrictToFinite M := by
    funext ω
    exact (infiniteStartCount_restrict G L M hcut ω).symm
  rw [heq]
  exact Measurable.of_discrete.comp (measurable_restrictToFinite M)

theorem dyadicCountLaw_coeff_eq_infinite_probability (N L k : ℕ) :
    (dyadicCountLaw N L).coeff k =
      infiniteRademacherMeasure.real {ω | infiniteStartCount (dyadicBlock N) L ω = k} := by
  classical
  have hcut : ∀ x ∈ dyadicBlock N, x + L ≤ dyadicCutoff N L := by
    intro x hx
    simp only [dyadicBlock, Finset.mem_Ico] at hx
    unfold dyadicCutoff
    omega
  unfold dyadicCountLaw
  rw [← finiteCylinder_weights_eq, finiteMeasure_countLaw_coeff]
  rw [← map_infiniteRademacherMeasure_restrictToFinite (dyadicCutoff N L)]
  rw [map_measureReal_apply (measurable_restrictToFinite _)
    (MeasurableSet.of_discrete)]
  congr 1
  ext ω
  change indicatorCount (dyadicBlock N) (fun x => startIndicator x L)
      (restrictToFinite (dyadicCutoff N L) ω) = k ↔ _
  rw [infiniteStartCount_restrict _ _ _ hcut]
  rfl

theorem dyadicCountLaw_realizes_infinite_count (N L : ℕ) :
    lawMeasure (dyadicCountLaw N L) (dyadicCountLaw_isProbability N L).1 =
      infiniteRademacherMeasure.map (infiniteStartCount (dyadicBlock N) L) := by
  apply Measure.ext_of_singleton
  intro k
  rw [lawMeasure_singleton, dyadicCountLaw_coeff_eq_infinite_probability]
  rw [Measure.map_apply (measurable_infiniteStartCount _ _) (MeasurableSet.singleton k)]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

end PaperP1.Model.InfiniteStarts
