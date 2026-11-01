module

public import PaperP1.Affine.ConditionalMass
public import PaperP1.Model.ConditionalRunRank
public import PaperP1.Model.InfiniteStarts

/-! # Conditional start probabilities under the original infinite prime-sign measure -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConditionalRunProbability

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.Algebra PaperP1.Probability PaperP1.ConditionalRunRank PaperP1.ConditionalWindowRank
  PaperP1.Model.InfiniteRademacher PaperP1.Model.InfiniteStarts
  PaperP1.Probability.InfiniteCylinderTransfer PaperP1.Probability.CylinderExpectations

local instance conditionalRunDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def finiteOldEvent {M : ℕ} (R : Finset ℕ) (a σ : SampleSpace M) : Prop :=
  ∀ n ∈ R, valueBit σ n = valueBit a n

def infiniteOldEvent {M : ℕ} (R : Finset ℕ) (a : SampleSpace M) (ω : InfiniteSample) : Prop :=
  ∀ n ∈ R, infiniteValueBit ω n = valueBit a n

def conditionalStartProbability {M : ℕ} (R : Finset ℕ) (a : SampleSpace M) (x L : ℕ) : ℝ :=
  infiniteRademacherMeasure.real {ω | infiniteOldEvent R a ω ∧ infiniteStartIndicator x L ω = true} /
    infiniteRademacherMeasure.real {ω | infiniteOldEvent R a ω}

theorem effectiveEvent_span_iff {V : Type*} [AddCommGroup V] [Module F₂ V]
    (T : Set (V →ₗ[F₂] F₂)) (a v : V) :
    effectiveEvent (Submodule.span F₂ T) a v ↔ ∀ f ∈ T, f v = f a := by
  constructor
  · intro h f hf
    exact h ⟨f, Submodule.subset_span hf⟩
  · intro h s
    refine Submodule.span_induction (fun f hf ↦ h f hf) (by simp)
      (fun f g _ _ hf hg ↦ ?_) (fun c f _ hf ↦ ?_) s.property
    · simp only [LinearMap.add_apply, hf, hg]
    · simp only [LinearMap.smul_apply, hf]

theorem oldRows_eq_span (M : ℕ) (R : Finset ℕ) :
    oldRows M R = Submodule.span F₂ ((fun n ↦ valueLinear M n) '' (R : Set ℕ)) := by
  rw [oldRows, oldSpan, Submodule.map_span]
  simp only [Set.image_image, parityPairing_parityVec]

theorem oldRows_event_iff {M : ℕ} (R : Finset ℕ) (a σ : SampleSpace M) :
    effectiveEvent (oldRows M R) a σ ↔ finiteOldEvent R a σ := by
  rw [oldRows_eq_span, effectiveEvent_span_iff]
  simp only [Set.forall_mem_image, mem_coe, valueLinear_apply, finiteOldEvent]

theorem oldEvent_restrict {M : ℕ} {R : Finset ℕ} (hR : ∀ n ∈ R, n ≤ M)
    (a : SampleSpace M) (ω : InfiniteSample) :
    finiteOldEvent R a (restrictToFinite M ω) ↔ infiniteOldEvent R a ω := by
  constructor
  · intro h n hn
    rw [← valueBit_restrictToFinite_eq_infiniteValueBit ω (hR n hn)]
    exact h n hn
  · intro h n hn
    rw [valueBit_restrictToFinite_eq_infiniteValueBit ω (hR n hn)]
    exact h n hn

theorem infiniteCylinder_event (M : ℕ) (E : SampleSpace M → Prop) :
    infiniteRademacherMeasure.real {ω | E (restrictToFinite M ω)} =
      finiteExpectation (cylinderProbability M).weight (fun σ ↦ if E σ then 1 else 0) := by
  calc
    _ = (infiniteRademacherMeasure.map (restrictToFinite M)).real {σ | E σ} :=
      (map_measureReal_apply (measurable_restrictToFinite M) MeasurableSet.of_discrete).symm
    _ = _ := by rw [map_infiniteRademacherMeasure_restrictToFinite, finiteCylinder_event]

theorem observation_probability {M : ℕ} {R : Finset ℕ} (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M) :
    infiniteRademacherMeasure.real {ω | infiniteOldEvent R a ω} = oldObservationMass (oldRows M R) a := by
  have heq : {ω | infiniteOldEvent R a ω} = {ω | finiteOldEvent R a (restrictToFinite M ω)} := by
    ext ω
    exact (oldEvent_restrict hR a ω).symm
  rw [heq, infiniteCylinder_event]
  unfold oldObservationMass
  congr 1
  funext σ
  rw [oldRows_event_iff]

theorem observation_probability_pos {M : ℕ} {R : Finset ℕ} (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M) :
    0 < infiniteRademacherMeasure.real {ω | infiniteOldEvent R a ω} := by
  rw [observation_probability hR]
  exact oldObservationMass_pos _ _

theorem conditionalStartProbability_eq_affine {M x L : ℕ} {R : Finset ℕ}
    (hL : 0 < L) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M) :
    conditionalStartProbability R a x L = conditionalAffineMass (oldRows M R) a (startSystem M x L) (startRhs L) := by
  have heq : {ω | infiniteOldEvent R a ω ∧ infiniteStartIndicator x L ω = true} =
      {ω | finiteOldEvent R a (restrictToFinite M ω) ∧ startIndicator x L (restrictToFinite M ω) = true} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [oldEvent_restrict hR, startIndicator_restrict_eq ω hcut]
  unfold conditionalStartProbability conditionalAffineMass
  rw [heq, infiniteCylinder_event M (fun σ ↦ finiteOldEvent R a σ ∧ startIndicator x L σ = true),
    observation_probability hR]
  congr 1
  apply congrArg (finiteExpectation (cylinderProbability M).weight)
  funext σ
  rw [oldRows_event_iff, startIndicator_eq_true_iff, ← startSystem_eq_startRhs_iff σ hL]
  split_ifs <;> rfl

theorem conditionalStartProbability_zero_or_pow {M x L : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hL : 0 < L) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M) :
    conditionalStartProbability R a x L = 0 ∨ conditionalStartProbability R a x L =
      (2 ^ conditionalNullity R (x - 1) (L + 1) : ℝ) / (2 ^ L : ℝ) := by
  rw [conditionalStartProbability_eq_affine hL hcut hR]
  simpa only [row_kernel_finrank hx hcut hR, Fintype.card_fin] using
    conditionalAffineMass_zero_or_pow (oldRows M R) a (startSystem M x L) (startRhs L)

theorem conditionalStartProbability_nominal {M x L : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hL : 0 < L) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) (a : SampleSpace M)
    (hcard : (supportedIndices R (x - 1) (L + 1)).card ≤ 1) :
    conditionalStartProbability R a x L = (2 ^ L : ℝ)⁻¹ := by
  rw [conditionalStartProbability_eq_affine hL hcut hR]
  have hzero : Module.finrank F₂ ((oldRows M R).comap (relationMap (startSystem M x L))) = 0 := by
    rw [row_kernel_finrank hx hcut hR]
    exact conditionalNullity_eq_zero_of_card_le_one hcard
  simpa only [Fintype.card_fin] using
    conditionalAffineMass_nominal_of_kernel_zero (oldRows M R) a (startSystem M x L) (startRhs L) hzero

end PaperP1.ConditionalRunProbability
