module

public import PaperP1.Model.CountObservables

/-! # Original positive run-start counts and their exact finite-cylinder expectations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveStarts

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.Algebra PaperP1.Probability PaperP1.CountObservables
  PaperP1.Probability.CylinderExpectations PaperP1.Probability.InfiniteCylinderTransfer

def indicator {M : ℕ} (x L : ℕ) (σ : SampleSpace M) : Bool :=
  startIndicator x L σ && decide (valueBit σ x = 0)

def infiniteIndicator (x L : ℕ) (ω : InfiniteSample) : Bool :=
  infiniteStartIndicator x L ω && decide (infiniteValueBit ω x = 0)

def infiniteCount (G : Finset ℕ) (L : ℕ) (ω : InfiniteSample) : ℕ :=
  indicatorCount G (fun x ↦ infiniteIndicator x L) ω

def exponentialMoment (G : Finset ℕ) (L : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, Real.exp (t * (infiniteCount G L ω : ℝ)) ∂infiniteRademacherMeasure

theorem indicator_restrict {M x L : ℕ} (ω : InfiniteSample) (hcut : x + L ≤ M) :
    indicator x L (restrictToFinite M ω) = infiniteIndicator x L ω := by
  simp only [indicator, infiniteIndicator, startIndicator_restrict_eq ω hcut,
    valueBit_restrictToFinite_eq_infiniteValueBit ω (show x ≤ M by omega)]

theorem count_restrict (G : Finset ℕ) (L M : ℕ) (hcut : ∀ x ∈ G, x + L ≤ M) (ω : InfiniteSample) :
    indicatorCount G (fun x ↦ indicator x L) (restrictToFinite M ω) = infiniteCount G L ω := by
  unfold indicatorCount infiniteCount
  exact sum_congr rfl (fun x hx ↦ congrArg Bool.toNat (indicator_restrict ω (hcut x hx)))

theorem measurable_infiniteCount (G : Finset ℕ) (L : ℕ) : Measurable (infiniteCount G L) := by
  let M := G.sup fun x ↦ x + L
  have hcut : ∀ x ∈ G, x + L ≤ M := fun x hx ↦ le_sup (f := fun x ↦ x + L) hx
  have heq : infiniteCount G L = (indicatorCount G (fun x ↦ indicator x L)) ∘ restrictToFinite M := by
    funext ω
    exact (count_restrict G L M hcut ω).symm
  rw [heq]
  exact Measurable.of_discrete.comp (measurable_restrictToFinite M)

theorem and_count_le {Ω ι : Type*} (G : Finset ι) (J K : ι → Ω → Bool) (ω : Ω) :
    indicatorCount G (fun i ω ↦ J i ω && K i ω) ω ≤ indicatorCount G J ω := by
  unfold indicatorCount
  apply sum_le_sum
  intro i _
  change (J i ω && K i ω).toNat ≤ (J i ω).toNat
  cases J i ω <;> cases K i ω <;> decide

theorem finiteCount_le_total {M : ℕ} (G : Finset ℕ) (L : ℕ) (σ : SampleSpace M) :
    indicatorCount G (fun x ↦ indicator x L) σ ≤ indicatorCount G (fun x ↦ startIndicator x L) σ :=
  and_count_le G (fun x ↦ startIndicator x L) (fun x σ ↦ decide (valueBit σ x = 0)) σ

theorem infiniteCount_le_total (G : Finset ℕ) (L : ℕ) (ω : InfiniteSample) :
    infiniteCount G L ω ≤ infiniteStartCount G L ω :=
  and_count_le G (fun x ↦ infiniteStartIndicator x L) (fun x ω ↦ decide (infiniteValueBit ω x = 0)) ω

theorem exponentialMoment_eq_finite {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (t : ℝ) :
    exponentialMoment G L t = finiteExpectation (cylinderProbability (dyadicCutoff N L)).weight
      (fun σ ↦ Real.exp (t * (indicatorCount G (fun x ↦ indicator x L) σ : ℝ))) := by
  unfold exponentialMoment
  have heq : (fun ω ↦ Real.exp (t * (infiniteCount G L ω : ℝ))) =
      (fun ω ↦ Real.exp (t * (indicatorCount G (fun x ↦ indicator x L)
        (restrictToFinite (dyadicCutoff N L) ω) : ℝ))) := by
    funext ω
    rw [count_restrict G L (dyadicCutoff N L) (dyadic_subset_cutoff hG)]
  rw [heq]
  exact infiniteCylinder_integral (dyadicCutoff N L) (fun σ : SampleSpace (dyadicCutoff N L) ↦
    Real.exp (t * (indicatorCount G (fun x ↦ indicator x L) σ : ℝ)))

end PaperP1.PositiveStarts
