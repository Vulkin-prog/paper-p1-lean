module

public import PaperP1.Probability.HereditaryActiveMaximum
public import PaperP1.Model.CompatibleNullityBound
public import PaperP1.Model.CompressedJointMoments
public import PaperP1.Model.CountObservables

/-! # The actual largest direct active subfamily has all-order Poisson bounds

The random maximum is constructed from the actual effective square-class
spaces and the original start indicators. Regularity supplies the common
marginal exactly; no fixed-order arithmetic theorem is used uniformly in r.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MaximumDirectActive

open Finset MeasureTheory PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Arithmetic PaperP1.Affine
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.HereditaryActiveMaximum PaperP1.Probability.InfiniteCylinderTransfer
  PaperP1.Probability.CylinderExpectations

local instance maximumDirectActiveMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance maximumDirectActiveDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def families (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) :=
  G.powerset.filter fun A ↦ runRelativeNullity L A = 0

def cutoff (G : Finset ℕ) (L : ℕ) : ℕ := G.sup fun x ↦ x + L

def finiteMaximum (G : Finset ℕ) (L M : ℕ) (σ : SampleSpace M) : ℕ :=
  maximumSize (families G L) (fun x ↦ startIndicator x L) σ

def maximum (G : Finset ℕ) (L : ℕ) (ω : InfiniteSample) : ℕ :=
  maximumSize (families G L) (fun x ↦ infiniteStartIndicator x L) ω

def mean (G : Finset ℕ) (L : ℕ) : ℝ := (G.card : ℝ) * (2 ^ L : ℝ)⁻¹

theorem mem_families {G A : Finset ℕ} {L : ℕ} :
    A ∈ families G L ↔ A ⊆ G ∧ runRelativeNullity L A = 0 := by
  simp only [families, mem_filter, mem_powerset]

theorem empty_mem (G : Finset ℕ) (L : ℕ) : ∅ ∈ families G L := by
  simp only [mem_families, empty_subset, runRelativeNullity_empty, and_self]

theorem families_hereditary (G : Finset ℕ) (L : ℕ) : Hereditary (families G L) := by
  intro A hA B hBA
  obtain ⟨hAG, hzero⟩ := mem_families.mp hA
  refine mem_families.mpr ⟨hBA.trans hAG, ?_⟩
  apply Nat.eq_zero_of_le_zero
  rw [← hzero]
  exact runRelativeNullity_mono L hBA

theorem maximum_attained (G : Finset ℕ) (L : ℕ) (ω : InfiniteSample) :
    ∃ A ⊆ G, runRelativeNullity L A = 0 ∧
      (∀ x ∈ A, infiniteStartIndicator x L ω = true) ∧ A.card = maximum G L ω := by
  obtain ⟨A, hA, hcard⟩ := HereditaryActiveMaximum.maximum_attained (families G L) (empty_mem G L)
    (fun x ↦ infiniteStartIndicator x L) ω
  obtain ⟨hAF, hactive⟩ := active_mem.mp hA
  obtain ⟨hAG, hzero⟩ := mem_families.mp hAF
  exact ⟨A, hAG, hzero, hactive, hcard.symm⟩

theorem finite_restrict (G : Finset ℕ) (L : ℕ) (ω : InfiniteSample) :
    finiteMaximum G L (cutoff G L) (restrictToFinite (cutoff G L) ω) = maximum G L ω := by
  apply maximum_congr
  intro A hA x hx
  exact startIndicator_restrict_eq ω (le_sup (f := fun x ↦ x + L) ((mem_families.mp hA).1 hx))

theorem observable_integral (G : Finset ℕ) (L : ℕ) (f : ℕ → ℝ) :
    (∫ ω, f (maximum G L ω) ∂infiniteRademacherMeasure) =
      finiteExpectation (cylinderProbability (cutoff G L)).weight
        (fun σ ↦ f (finiteMaximum G L (cutoff G L) σ)) := by
  calc
    _ = ∫ ω, f (finiteMaximum G L (cutoff G L) (restrictToFinite (cutoff G L) ω))
        ∂infiniteRademacherMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ congrArg f (finite_restrict G L ω).symm
    _ = _ := infiniteCylinder_integral (cutoff G L) (fun σ ↦ f (finiteMaximum G L (cutoff G L) σ))

theorem observable_integrable (G : Finset ℕ) (L : ℕ) (f : ℕ → ℝ) :
    Integrable (fun ω ↦ f (maximum G L ω)) infiniteRademacherMeasure := by
  have hi := (integrable_finite_function
    (infiniteRademacherMeasure.map (restrictToFinite (cutoff G L)))
    (fun σ ↦ f (finiteMaximum G L (cutoff G L) σ))).comp_measurable
      (measurable_restrictToFinite (cutoff G L))
  simpa only [Function.comp_def, finite_restrict] using hi

theorem maximum_le_count (G : Finset ℕ) (L : ℕ) (ω : InfiniteSample) :
    maximum G L ω ≤ infiniteStartCount G L ω :=
  HereditaryActiveMaximum.maximum_le_count G (families G L)
    (fun _ hA ↦ (mem_families.mp hA).1) _ ω

theorem mean_eq_actual {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ RegularStarts.regularStarts N L) : mean G L = CountObservables.countMoment G L 1 := by
  rw [CountObservables.countMoment_one (hG.trans (RegularStarts.regularStarts_subset N L))]
  calc
    _ = ∑ _x ∈ G, (2 ^ L : ℝ)⁻¹ := by rw [sum_const, nsmul_eq_mul]; rfl
    _ = _ := by
      apply sum_congr rfl
      intro x hx
      have hxpos : 0 < x := by
        have h := (mem_Ico.mp ((RegularStarts.regularStarts_subset N L) (hG hx))).1
        omega
      exact (RegularStarts.marginal_on_regular hxpos hL (hG hx)).symm

theorem finite_joint {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ RegularStarts.regularStarts N L) (A : Finset ℕ) (hA : A ∈ families G L) :
    finiteJointMoment (cylinderProbability (cutoff G L)) (fun x ↦ startIndicator x L) A =
      ((2 ^ L : ℝ)⁻¹) ^ A.card := by
  obtain ⟨hAG, hzero⟩ := mem_families.mp hA
  have hcut (x : ℕ) (hx : x ∈ A) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) (hAG hx)
  rw [← infiniteJointMoment_eq_finite (cutoff G L) L A hcut]
  exact CompressedJointMoments.regular_direct_joint hN hL A (hAG.trans hG) hzero

theorem expected_choose_binomial {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ RegularStarts.regularStarts N L) (r : ℕ) :
    (∫ ω, ((maximum G L ω).choose r : ℝ) ∂infiniteRademacherMeasure) ≤
      (G.card.choose r : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ r := by
  rw [observable_integral G L (fun n ↦ (n.choose r : ℝ))]
  exact expected_choose_binomial_bound _ G (families G L) (empty_mem G L) (families_hereditary G L)
    (fun _ hA ↦ (mem_families.mp hA).1) _ _ (by positivity)
    (fun A hA ↦ (finite_joint hN hL G hG A hA).le) r

theorem expected_choose_poisson {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ RegularStarts.regularStarts N L) (r : ℕ) :
    (∫ ω, ((maximum G L ω).choose r : ℝ) ∂infiniteRademacherMeasure) ≤ mean G L ^ r / r.factorial := by
  rw [observable_integral G L (fun n ↦ (n.choose r : ℝ))]
  exact expected_choose_poisson_bound _ G (families G L) (empty_mem G L) (families_hereditary G L)
    (fun _ hA ↦ (mem_families.mp hA).1) _ _ (by positivity)
    (fun A hA ↦ (finite_joint hN hL G hG A hA).le) r

theorem expected_factorial {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ RegularStarts.regularStarts N L) (r : ℕ) :
    (∫ ω, ((maximum G L ω).descFactorial r : ℝ) ∂infiniteRademacherMeasure) ≤ mean G L ^ r := by
  rw [observable_integral G L (fun n ↦ (n.descFactorial r : ℝ))]
  exact expected_factorial_bound _ G (families G L) (empty_mem G L) (families_hereditary G L)
    (fun _ hA ↦ (mem_families.mp hA).1) _ _ (by positivity)
    (fun A hA ↦ (finite_joint hN hL G hG A hA).le) r

theorem expected_power_binomial {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ RegularStarts.regularStarts N L) (s : ℝ) (hs : 1 ≤ s) :
    (∫ ω, s ^ maximum G L ω ∂infiniteRademacherMeasure) ≤
      (1 + (2 ^ L : ℝ)⁻¹ * (s - 1)) ^ G.card := by
  rw [observable_integral]
  exact expected_power_binomial_bound _ G (families G L) (empty_mem G L) (families_hereditary G L)
    (fun _ hA ↦ (mem_families.mp hA).1) _ _ (by positivity)
    (fun A hA ↦ (finite_joint hN hL G hG A hA).le) s hs

theorem expected_power_exponential {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ RegularStarts.regularStarts N L) (s : ℝ) (hs : 1 ≤ s) :
    (∫ ω, s ^ maximum G L ω ∂infiniteRademacherMeasure) ≤ Real.exp ((s - 1) * mean G L) := by
  rw [observable_integral]
  exact expected_power_exponential_bound _ G (families G L) (empty_mem G L) (families_hereditary G L)
    (fun _ hA ↦ (mem_families.mp hA).1) _ _ (by positivity)
    (fun A hA ↦ (finite_joint hN hL G hG A hA).le) s hs

theorem tail_probability_eq_finite (G : Finset ℕ) (L r : ℕ) :
    infiniteRademacherMeasure.real {ω | r ≤ maximum G L ω} =
      finiteExpectation (cylinderProbability (cutoff G L)).weight
        (fun σ ↦ if r ≤ finiteMaximum G L (cutoff G L) σ then (1 : ℝ) else 0) := by
  have hset : {ω | r ≤ maximum G L ω} =
      restrictToFinite (cutoff G L) ⁻¹' {σ | r ≤ finiteMaximum G L (cutoff G L) σ} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, finite_restrict]
  rw [hset, ← map_measureReal_apply (measurable_restrictToFinite (cutoff G L))
    ((Set.to_countable _).measurableSet), map_infiniteRademacherMeasure_restrictToFinite]
  exact finiteCylinder_event (cutoff G L) _

theorem tail_probability {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (G : Finset ℕ)
    (hG : G ⊆ RegularStarts.regularStarts N L) (r : ℕ) :
    infiniteRademacherMeasure.real {ω | r ≤ maximum G L ω} ≤ mean G L ^ r / r.factorial := by
  rw [tail_probability_eq_finite]
  exact tail_bound _ G (families G L) (empty_mem G L) (families_hereditary G L)
    (fun _ hA ↦ (mem_families.mp hA).1) _ _ (by positivity)
    (fun A hA ↦ (finite_joint hN hL G hG A hA).le) r

end PaperP1.MaximumDirectActive
